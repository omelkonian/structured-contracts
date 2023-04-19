{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init; open SetAsType
open import Prelude.InferenceRules
open import Prelude.Lists.Sums
open import Prelude.DecEq
open import Prelude.Maps

open import SmallStep
open import UTxO

-- ** LEDGER
data _⊢_—⟨_∣LEDGER⟩→_ : SSRel (TxInfo , UTxO , Tx) where

  ApplyTx : let utxo′ = applyTx tx utxo in
    T (checkTx txi utxo tx)
    ──────────────────────────────────
    txi ⊢ utxo —⟨ tx ∣LEDGER⟩→ utxo′

-- ** POV
data _⊢_—⟨_∣POV⟩→_ : SSRel (TxInfo , Value , Value) where

  UpdateValTotal : let i = mint txi in
    ──────────────────────────────────
    txi ⊢ v —⟨ i ∣POV⟩→ (v + i)

-- ** LEDGER ≼ POV

π : UTxO → Value
π = ∑ℕ ∘ map value ∘ values

LEDGER-reifies-POV : _⊢_—⟨_∣LEDGER⟩→_ ≼ _⊢_—⟨_∣POV⟩→_
LEDGER-reifies-POV = record
  { πₛ = π
  ; πᵢ = forge
  ; implements = proof
  }
  where
    proof : ∀ Γ s i s′ → Γ ⊢ s —⟨ i ∣LEDGER⟩→ s′ → Γ ⊢ π s —⟨ forge i ∣POV⟩→ π s′
    proof txi s tx .(applyTx tx s) (ApplyTx p)
      -- GOAL:
      with isValidTx? tx s
    ... | yes valid with txi ≟ mkTxInfo tx (resolved valid) | p
    ... | yes refl | _
      = QED
      where
        H₁ : forge tx ≡ mint txi
        H₁ = refl

        H₂ : π (applyTx tx s) ≡ π s + forge tx
        H₂ =
          begin
            π (applyTx tx s)
          ≡⟨⟩
            π ((s ─ᵏˢ outputRefs tx) ∪ utxoTx tx)
          ≡⟨ {!preservesValues valid!} ⟩
            π s + forge tx
          ∎ where open ≡-Reasoning

        QED : txi ⊢ π s —⟨ forge tx ∣POV⟩→ π (applyTx tx s)
        QED rewrite H₁ | H₂ = UpdateValTotal {txi = txi} {v = π s}

POV :
  txi ⊢ utxo —⟨ tx ∣LEDGER⟩→ utxo′
  ────────────────────────────────
  π utxo′ ≡ π utxo + forge tx
POV {txi} p with LEDGER-reifies-POV .implements txi _ _ _ p
... | p = {!!}
-- ... | UpdateValTotal = refl
