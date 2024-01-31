module POV where

open import Prelude
open import UTxO

data _⊢_—⟨_∣POV⟩→_ : SSRel TxInfo Value Value where

  UpdateValTotal : let i = mint txi in
    ──────────────────────────────────
    txi ⊢ v —⟨ i ∣POV⟩→ (v + i)

LEDGER-reifies-POV : _⊢_—⟨_∣LEDGER⟩→_ ≼ _⊢_—⟨_∣POV⟩→_
LEDGER-reifies-POV = record
  { πₛ = π
  ; πᵢ = forge
  ; implements = proof
  }
  where
    π = totalValue

    proof : ∀ Γ s i s′ → Γ ⊢ s —⟨ i ∣LEDGER⟩→ s′ → Γ ⊢ π s —⟨ i .forge ∣POV⟩→ π s′
    proof txi s tx .(applyTx tx s) (ApplyTx p)
      with isValidTx? tx s
    ... | yes valid with txi ≟ mkTxInfo tx (resolved valid) | p
    ... | yes refl | _
      = QED
      where
        H : π (applyTx tx s) ≡ π s + tx .forge
        H =
          begin
            π (applyTx tx s)
          ≡⟨⟩
            π ((s ─ᵏˢ outputRefs tx) ∪ utxoTx tx)
          ≡⟨ nextValue≡ valid ⟩
            (π s + outs) ∸ ins
          ≡˘⟨ cong (λ ◆ → (π s + ◆) ∸ ins) $ preservesValues valid ⟩
            (π s + (tx .forge + ins)) ∸ ins
          ≡˘⟨ cong (_∸ ins) $ Nat.+-assoc (π s) _ _ ⟩
            ((π s + tx .forge) + ins) ∸ ins
          ≡⟨ Nat.m+n∸n≡m _ ins ⟩
            π s + tx .forge
          ∎ where open ≡-Reasoning
                  ins = ∑ (resolvedInputs valid) (value ∘ proj₂)
                  outs = ∑ (tx .outputs) value

        QED : txi ⊢ π s —⟨ tx .forge ∣POV⟩→ π (applyTx tx s)
        QED rewrite H = UpdateValTotal {txi = txi} {v = π s}

POV :
  txi ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′
  ──────────────────────────────────────────────
  totalValue utxos′ ≡ totalValue utxos + tx .forge
POV = viewPOV ∘ LEDGER-reifies-POV .implements _ _ _ _
  where
    viewPOV : txi ⊢ v —⟨ v″ ∣POV⟩→ v′ → v′ ≡ v + v″
    viewPOV UpdateValTotal = refl
