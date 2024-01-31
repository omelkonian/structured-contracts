module Toggle where

open import Prelude
open import Prelude.Ord
open import EUTxO

private variable b b′ : Bool

pattern ⋆ = false
pattern toggle = true

data _⊢_—⟨_∣TOGGLE⟩→_ : SSRel ⊤ (Bool × Bool) Bool where
  DoNothing :
    ────────────────────────────────────
    _ ⊢ (b , b′) —⟨ ⋆ ∣TOGGLE⟩→ (b , b′)

  Toggle :
    ─────────────────────────────────────────
    _ ⊢ (b , b′) —⟨ toggle ∣TOGGLE⟩→ (b′ , b)
