module EUTxO where

open import Prelude
open import Prelude.Lists.Membership

PolicyID  = ℕ
TokenName = ℕ
Quantity  = ℕ

Tokens = Map⟨ TokenName ↦ Quantity ⟩
Value  = Map⟨ PolicyID  ↦ Tokens ⟩
Slot  = ℕ
DATA  = ℕ
Hash  = ℕ

Address   = Hash
PubKey    = Hash
Signature = Hash

variable
  v v′ v″ : Value
  slot : Slot
postulate instance
  Ord-Tokens    : Ord Tokens
  DecOrd-Tokens : DecOrd Tokens
instance
  Semigroup-ℕ  = Semigroup-ℕ-+
  Monoid-ℕ     = Monoid-ℕ-+
  Monoid-Value : Monoid Tokens
  Monoid-Value = λ where .ε → ∅

private variable A : Type ℓ
postulate
  _♯ : A → Hash
  ♯-injective : Injective≡ {A = A} _♯

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

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : Hash
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

record InputInfo : Type where
  field output        : TxOutput
        outputRef     : TxOutputRef
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
variable tx : Tx
postulate checkSig : Tx → PubKey → Hash → Type

-- A ledger is a list of transactions.
L = List Tx
variable l : L

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
resolveInputs tx rtx = mapWith∈ (tx .inputs) λ {i} i∈ →
  i , rtx (∈-map⁺ outputRef i∈)

mkInputInfo : ResolvedInput → InputInfo
mkInputInfo (i , o) = record
  { output        = o
  ; outputRef     = i .outputRef
  ; validatorHash = i .validator ♯
  ; redeemerHash  = i .redeemer ♯ }

mkTxInfo : ∀ tx → Resolved tx → TxInfo
mkTxInfo tx rtx = record
  { inputs  = mkInputInfo <$> resolveInputs tx rtx
  ; outputs = tx .outputs
  ; mint    = tx .mint }

postulate
  resolvedOutRefs≡ : ∀ tx (rtx : Resolved tx) →
      (InputInfo.outputRef ∘ mkInputInfo <$> resolveInputs tx rtx)
    ≡ (outputRef <$> tx .inputs)

--

-- The state of a ledger maps output references locked by a validator to a value.
UTxO = Map⟨ TxOutputRef ↦ TxOutput ⟩
variable utxos utxos′ : UTxO

mkUtxo : ∀ {out} tx → out ∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈) , out

utxoTx : Tx → UTxO
utxoTx tx = fromList $ mapWith∈ (tx .outputs) (mkUtxo tx)

postulate
  ∉utxoTx        : ∀ {or} → tx ♯ ≢ or .txId → or ∉ᵈ utxoTx tx
  utxoTx-values≡ : ∀ {tx} → values (utxoTx tx) ≡ tx .outputs

∑ᵐ : UTxO → Value
∑ᵐ = ∑ ∘ map value ∘ values

postulate ∑ᵐ-∪ : ∑ᵐ (utxos ∪ utxos′) ≡ ∑ᵐ utxos ∪ ∑ᵐ utxos′

∑outs≡ : ∑ᵐ (utxoTx tx) ≡ ∑ (value <$> tx .outputs)
∑outs≡ = cong (∑ ∘ map value) utxoTx-values≡

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

  rtx : Resolved tx
  rtx = (utxos ‼_) ∘ L.All.lookup validOutputRefs

  txInfo         = mkTxInfo      tx rtx
  resolvedInputs = resolveInputs tx rtx

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

  -- derived properties
  open ≡-Reasoning

  outRefs≡ : (InputInfo.outputRef <$> txInfo .TxInfo.inputs)
           ≡ outputRefs tx
  outRefs≡ =
    begin
      InputInfo.outputRef <$> txInfo .TxInfo.inputs
    ≡⟨⟩
      InputInfo.outputRef <$> (mkInputInfo <$> resolvedInputs)
    ≡˘⟨ L.map-compose resolvedInputs ⟩
      InputInfo.outputRef ∘ mkInputInfo <$> resolvedInputs
    ≡⟨ resolvedOutRefs≡ tx rtx ⟩
      outputRef <$> tx .inputs
    ≡⟨⟩
      outputRefs tx
    ∎

  ∑utxoTx≡ : ∑ᵐ (utxoTx tx)
           ≡ tx .mint ∪ ∑ (value ∘ proj₂ <$> resolvedInputs)
  ∑utxoTx≡ = begin
    ∑ᵐ (utxoTx tx)                                  ≡⟨ ∑outs≡ ⟩
    ∑ (value <$> tx .outputs)                       ≡˘⟨ preservesValues ⟩
    tx .mint ∪ ∑ (value ∘ proj₂ <$> resolvedInputs) ∎

  postulate
    ∑utxos─∪≡ : ∑ᵐ (utxos ─ᵏˢ outputRefs tx)
              ∪ ∑ (value ∘ proj₂ <$> resolvedInputs)
              ≡ ∑ᵐ utxos

open IsValidTx public

postulate isValidTx? : ∀ slot tx s → Dec (IsValidTx slot tx s)

isValidTx : Slot → Tx → UTxO → Bool
isValidTx slot tx s = ⌊ isValidTx? slot tx s ⌋

checkTx : Slot → UTxO → Tx → Bool
checkTx slot s tx = ⌊ isValidTx? slot tx s ⌋

-- ** LEDGER small-step relation
data _⊢_—⟨_∣LEDGER⟩→_ : SSRel Slot UTxO Tx where

  ApplyTx : let utxos′ = applyTx tx utxos in
    T (checkTx slot utxos tx)
    ───────────────────────────────────
    slot ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′
