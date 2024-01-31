module UTxO where

open import Prelude

Value   = ℕ
HashId  = ℕ
Slot    = ℕ
Address = HashId
postulate _♯ : ∀ {A : Type ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

∑ : ∀ {A : Type} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

record TxOutput : Type where
  constructor _at_
  field value    : Value
        address  : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

record InputInfo : Type where
  field outputRef     : TxOutput
        -- NB: the actual implementation also keeps references here
        validatorHash : HashId
        redeemerHash  : HashId
unquoteDecl DecEq-InputInfo = DERIVE DecEq [ quote InputInfo , DecEq-InputInfo ]

record TxInfo : Type where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value
unquoteDecl DecEq-TxInfo = DERIVE DecEq [ quote TxInfo , DecEq-TxInfo ]

module CommonInfo (TxOutputRef : Type) where

  record TxInput : Type where
    field outputRef : TxOutputRef
          validator : TxInfo → DATA → Bool
          redeemer  : DATA
  open TxInput public

  record Tx : Type where
    field inputs  : List TxInput
          outputs : List TxOutput
          forge   : Value
  open Tx public

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
    ; forge   = tx .forge }

All-syntax = All
syntax All-syntax (λ i → P) xs = ∀[ i ∈ xs ] P

Any-syntax = Any
syntax Any-syntax (λ i → P) xs = ∃[ i ∈ xs ] P

--

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : HashId
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
totalValue = ∑ℕ ∘ map value ∘ values

applyTx : Tx → (UTxO → UTxO)
applyTx tx utxo = (utxo ─ᵏˢ outputRefs tx) ∪ utxoTx tx

utxo : L → UTxO
utxo = λ where
  [] → ∅
  (tx ∷ l) → applyTx tx (utxo l)

record IsValidTx (tx : Tx) (utxos : UTxO) : Type where
  field
    noDoubleSpending :
      ·Unique (outputRefs tx)

    validOutputRefs :
      ∀[ ref ∈ outputRefs tx ]
        (ref ∈ᵈ utxos)

  resolved : Resolved tx
  resolved = (utxos ‼_) ∘ L.All.lookup validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved

  field
    preservesValues :
      tx .forge + ∑ resolvedInputs (value ∘ proj₂) ≡ ∑ (tx .outputs) value

    allInputsValidate :
      ∀[ i ∈ tx .inputs ]
        T (i .validator txInfo (i .redeemer))

    validateValidHashes :
      ∀[ (i , o) ∈ resolvedInputs ]
        (o .address ≡ i .validator ♯)

  postulate
    nextValue≡ :
      totalValue ((utxos ─ᵏˢ outputRefs tx) ∪ utxoTx tx)
      ≡ (totalValue utxos + ∑ (tx .outputs) value) ∸ ∑ resolvedInputs (value ∘ proj₂)

open IsValidTx public

instance
  ·Valid : ∀ {tx s} → · IsValidTx tx s
  ·Valid {s = _ ⊣ ·uniq} .∀≡
    (record { noDoubleSpending = ndp
            ; validOutputRefs = vor
            ; preservesValues = pv
            ; allInputsValidate = aiv
            ; validateValidHashes = vvh
            })
    (record { noDoubleSpending = ndp′
            ; validOutputRefs = vor′
            ; preservesValues = pv′
            ; allInputsValidate = aiv′
            ; validateValidHashes = vvh′
            })
    with uniq ← recompute dec ·uniq
    rewrite ∀≡ ndp ndp′
          | L.All.irrelevant (∈-irr uniq) vor vor′
          | ∀≡ pv pv′
          | L.All.irrelevant B.T-irrelevant aiv aiv′
          | ∀≡ vvh vvh′
          = refl

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx s@(_ ⊣ ·uniq)
  with uniq ← recompute dec ·uniq
  with dec
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes ndp with dec
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes vor with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; preservesValues = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes pv with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; allInputsValidate = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes aiv with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; validateValidHashes = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes vvh = yes record
  { noDoubleSpending = ndp
  ; validOutputRefs = vor
  ; preservesValues = pv
  ; allInputsValidate = aiv
  ; validateValidHashes = vvh }

isValidTx : Tx → UTxO → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋

checkTx : TxInfo → UTxO → Tx → Bool
checkTx txi s tx with isValidTx? tx s
... | no _  = false
... | yes valid = txi == mkTxInfo tx (resolved valid)

mint : TxInfo → Value
mint = TxInfo.forge

variable
  tx : Tx
  l : L
  txi : TxInfo
  utxos utxos′ : UTxO
  v v′ v″ : Value

-- ** LEDGER small-step relation
data _⊢_—⟨_∣LEDGER⟩→_ : SSRel TxInfo UTxO Tx where

  ApplyTx : let utxos′ = applyTx tx utxos in
    T (checkTx txi utxos tx)
    ──────────────────────────────────
    txi ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′

-- ** TX-LEDGER small-step relation
data _⊢_—⟨_∣TX-LEDGER⟩→_ : SSRel ⊤ L Tx where

  ApplyTx :
    IsValidTx tx (utxo l)
    ─────────────────────────────────
    _ ⊢ l —⟨ tx ∣TX-LEDGER⟩→ (tx ∷ l)

postulate
  TX-LEDGER-reifies-LEDGER : _⊢_—⟨_∣TX-LEDGER⟩→_ ≼ _⊢_—⟨_∣LEDGER⟩→_
-- TX-LEDGER-reifies-LEDGER = record
--   { πₑ = λ _ s tx → mkTxInfo tx {!resolved valid!} -- (resolved valid)
--   ; πₛ = π
--   ; πᵢ = id
--   ; implements = proof
--   }
--   where
--     π = utxo

--     getValid : ∀ {Γ l tx l′} → Γ ⊢ l —⟨ tx ∣TX-LEDGER⟩→ l′ → IsValidTx tx (utxo l)
--     getValid (ApplyTx val) = val

--     proof : ∀ Γ l tx l′ →
--       (l→ : Γ ⊢ l —⟨ tx ∣TX-LEDGER⟩→ l′) →
--       ──────────────────────────────────────
--       mkTxInfo tx {!resolved $ getValid l→ !} ⊢ utxo l —⟨ tx ∣LEDGER⟩→ utxo l′
--     proof _ l tx .(tx ∷ l) (ApplyTx val) = {!!}
