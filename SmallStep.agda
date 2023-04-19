open import Prelude.Init; open SetAsType

-- small-step relations
SSRel : Type × Type × Type → Type₁
SSRel (Env , State , Input) = Env → State → Input → State → Type

private variable
  Env S S′ I I′ : Type
  Γ Δ : Env
  s s′ : S
  i i′ : I

-- 𝔸 reifies 𝔹
record _≼_ (𝔸 : SSRel (Env , S , I)) (𝔹 : SSRel (Env , S′ , I′)) : Type where
  field
    πₛ : S → S′
    πᵢ : I → I′
    implements : ∀ Γ s i s′ → 𝔸 Γ s i s′ → 𝔹 Γ (πₛ s) (πᵢ i) (πₛ s′)
open _≼_ public
