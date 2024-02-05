open import Prelude hiding (id; _~ˢ_; _~ᵉ_)
-- open import UTxO
open import EUTxO

record StrucSimulation S I (_⊢_—⟨_∣STRUC⟩→_ : SSRel ⊤ S I) : Type where
  field
    πˢ : UTxO → Maybe S
    πⁱ : Tx → I

  _~ˢ_ : UTxO → S → Type
  utxo ~ˢ s = πˢ utxo ≡ just s

  _~ᵉ_ : Slot × Tx → ⊤ × I → Type
  _~ᵉ_ = λ (_ , tx) (tt , i) → πⁱ tx ≡ i

  field
    simulates : ∀ Γ Γ′ s u i i′ s′ →
      ∙ Γ ⊢ s —⟨ i ∣LEDGER⟩→ s′
      ∙ (Γ , i) ~ᵉ (Γ′ , i′)
      ∙ s ~ˢ u
        ─────────────────────────────────
        ∃ λ u′ → s′ ~ˢ u′
               × Γ′ ⊢ u —⟨ i′ ∣STRUC⟩→ u′

  LEDGER≼STRUC : _⊢_—⟨_∣LEDGER⟩→_ ≼′ _⊢_—⟨_∣STRUC⟩→_
  LEDGER≼STRUC = record
    { _~ˢ_ = _~ˢ_
    ; _~ᵉ_ = _~ᵉ_
    ; implements′ = simulates
    }
