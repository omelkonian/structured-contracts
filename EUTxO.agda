module EUTxO where

open import Prelude
open import Prelude.Ord
open import Prelude.ToList

PolicyID  = ℕ
TokenName = ℕ
Quantity  = ℕ

Value = Map⟨ PolicyID ↦ Map⟨ TokenName ↦ Quantity ⟩ ⟩
Slot  = ℕ
DATA  = ℕ
Hash  = ℕ

Address   = Hash
PubKey    = Hash
Signature = Hash
postulate _♯ : ∀ {A : Type ℓ} → A → Hash

∑ : List Value → Value
∑ [] = ∅
∑ (v ∷ vs) = v ∪ ∑ vs

record TxOutput : Type where
  constructor _at_
  field value    : Value
        address  : Address
        datum    : DATA
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

record InputInfo : Type where
  field outputRef     : TxOutput
        validatorHash : Hash
        redeemerHash  : Hash
unquoteDecl DecEq-InputInfo = DERIVE DecEq [ quote InputInfo , DecEq-InputInfo ]

record TxInfo : Type where
  field inputs  : List InputInfo
        outputs : List TxOutput
        mint   : Value
unquoteDecl DecEq-TxInfo = DERIVE DecEq [ quote TxInfo , DecEq-TxInfo ]

Redeemer = DATA
Datum    = DATA
ScriptValidator = TxInfo {-× Hash-} → Datum → Redeemer → Bool
MintingPolicy   = TxInfo × PolicyID → Redeemer → Bool
postulate instance DecEq-MP : DecEq MintingPolicy

module CommonInfo (TxOutputRef : Type) where

  record TxInput : Type where
    field outputRef : TxOutputRef
          validator : TxInfo → DATA → DATA → Bool
          redeemer datum : DATA
  open TxInput public

  record Tx : Type where
    field inputs   : List TxInput
          outputs  : List TxOutput
          mint     : Value
          mintRdrs : Map⟨ MintingPolicy ↦ Redeemer ⟩
          interval : Slot × Slot
          sigs     : Map⟨ PubKey ↦ Hash ⟩
  open Tx public
  postulate checkSig : Tx → PubKey → Hash → Type

  -- A ledger is a list of transactions.
  L = List Tx

  instance
    Semigroup-L : Semigroup L
    Semigroup-L ._◇_ = _++_

    Monoid-L : Monoid L
    Monoid-L .ε = []

  -- Auxiliary definitions.

  outputRefs : Tx → List TxOutputRef
  outputRefs = map outputRef ∘ inputs

  Resolved : Pred₀ Tx
  Resolved tx = ∀ {r} → r ∈ outputRefs tx → TxOutput

  ResolvedInput  = TxInput × TxOutput
  ResolvedInputs = List ResolvedInput

  resolveInputs : ∀ tx → Resolved tx → ResolvedInputs
  resolveInputs tx resolvedTx = mapWith∈ (tx .inputs) λ {i} i∈ →
    i , resolvedTx (∈-map⁺ outputRef i∈)

  mkInputInfo : ResolvedInput → InputInfo
  mkInputInfo (i , o) = record
    { outputRef     = o
    ; validatorHash = i .validator ♯
    ; redeemerHash  = i .redeemer ♯ }

  mkTxInfo : ∀ (tx : Tx) → Resolved tx → TxInfo
  mkTxInfo tx resolvedTx = record
    { inputs  = mkInputInfo <$> resolveInputs tx resolvedTx
    ; outputs = tx .outputs
    ; mint   = tx .mint }

All-syntax = All
syntax All-syntax (λ i → P) xs = ∀[ i ∈ xs ] P

Any-syntax = Any
syntax Any-syntax (λ i → P) xs = ∃[ i ∈ xs ] P

--

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : Hash
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

open CommonInfo TxOutputRef public

-- The state of a ledger maps output references locked by a validator to a value.
UTxO = Map⟨ TxOutputRef ↦ TxOutput ⟩

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈) , out

utxoTx : Tx → UTxO
utxoTx tx = fromList $ L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

totalValue : UTxO → Value
totalValue = ∑ ∘ map value ∘ values

applyTx : Tx → (UTxO → UTxO)
applyTx tx utxo = (utxo ─ᵏˢ outputRefs tx) ∪ utxoTx tx

utxo : L → UTxO
utxo = λ where
  [] → ∅
  (tx ∷ l) → applyTx tx (utxo l)

record IsValidTx (slot : Slot) (tx : Tx) (utxos : UTxO) : Type where
  field
    noDoubleSpending :
      ·Unique (outputRefs tx)

    validInterval : let (from , to) = tx .interval in
      (from ≤ slot) × (slot ≤ to)

    validOutputRefs :
      ∀[ ref ∈ outputRefs tx ]
        (ref ∈ᵈ utxos)

  resolved : Resolved tx
  resolved = (utxos ‼_) ∘ L.All.lookup validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved

  field
    preservesValues :
      tx .mint ∪ ∑ (value ∘ proj₂ <$> resolvedInputs) ≡ ∑ (value <$> tx .outputs)

  -- ** script validation
    allInputsValidate :
      ∀[ i ∈ tx .inputs ]
        T (i .validator txInfo (i .datum) (i .redeemer))

    validateValidHashes :
      ∀[ (i , o) ∈ resolvedInputs ]
        (o .address ≡ i .validator ♯)

  -- ** minting policies
    validMintRedeemers :
      keys (tx .mint) ⊆ (_♯ <$> keys (tx .mintRdrs))

    allPoliciesValidate :
      ∀[ (p , r) ∈ toList (tx .mintRdrs) ]
        T (p (txInfo , p ♯) r)

  -- ** signatures
    validSignatures :
      ∀[ (pk , s) ∈ toList (tx .sigs) ]
        checkSig tx pk s

open IsValidTx public

postulate isValidTx? : ∀ slot tx s → Dec (IsValidTx slot tx s)

isValidTx : Slot → Tx → UTxO → Bool
isValidTx slot tx s = ⌊ isValidTx? slot tx s ⌋

checkTx : TxInfo → Slot → UTxO → Tx → Bool
checkTx txi slot s tx with isValidTx? slot tx s
... | no _  = false
... | yes valid = txi == mkTxInfo tx (resolved valid)

variable
  tx : Tx
  l : L
  txi : TxInfo
  slot : Slot
  utxos utxos′ : UTxO
  v v′ v″ : Value

-- ** LEDGER small-step relation
data _⊢_—⟨_∣LEDGER⟩→_ : SSRel Slot UTxO Tx where

  ApplyTx : let utxos′ = applyTx tx utxos in
    T (checkTx txi slot utxos tx)
    ──────────────────────────────────
    slot ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′
