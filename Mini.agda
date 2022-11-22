open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.InferenceRules

variable
  n m : ℕ
  w q : String

SSRel : Type → Type → Type₁
SSRel S I = S → I → S → Type

module SM where
  S = ℕ × String
  data I : Type where
    inc incˡ incʳ : I
  data _—⟨_⟩→_ : SSRel S I where
    inc  : (n , w) —⟨ inc  ⟩→ (n + 1 , w ◇ ".")
    incˡ : (n , w) —⟨ incˡ ⟩→ (n + 1 , w)
    incʳ : (n , w) —⟨ incʳ ⟩→ (n , w ◇ ".")

module SMˡ where
  data I : Type where
    inc : I
  data _—⟨_⟩→_ : SSRel ℕ I where
    inc : n —⟨ inc ⟩→ (n + 1)

module SMʳ where
  data I : Type where
    inc : I
  data _—⟨_⟩→_ : SSRel String I where
    inc : w —⟨ inc ⟩→ (w ◇ ".")

record _~_ {S I S′ I′} (_—⟨_⟩→_ : SSRel S I) (_—⟨_⟩→′_ : SSRel S′ I′) : Type where
  field
    π : S → S′
    π-onto : Surjective≡ {A = S} π
    ψ : I → I′
    ψ-onto : Surjective≡ {A = I} ψ

    Simulates : ∀ {s i s′} →
      s —⟨ i ⟩→ s′
      ───────────────────────
        (π s ≡ π s′)
      ⊎ (π s —⟨ ψ i ⟩→′ π s′)
open _~_ public

_ : SM._—⟨_⟩→_ ~ SMˡ._—⟨_⟩→_
_ = let open SM; open SMˡ in λ where
  .π → proj₁
  .π-onto _ → (_ , "") , refl
  .ψ _ → inc
  .ψ-onto inc → inc , refl
  .Simulates → λ where
     inc → inj₂ inc
     incˡ → inj₂ inc
     incʳ → inj₁ refl

_ : SM._—⟨_⟩→_ ~ SMʳ._—⟨_⟩→_
_ = let open SM; open SMʳ in λ where
  .π → proj₂
  .π-onto _ → (0 , _) , refl
  .ψ _ → inc
  .ψ-onto inc → inc , refl
  .Simulates → λ where
     inc → inj₂ inc
     incˡ → inj₁ refl
     incʳ → inj₂ inc
