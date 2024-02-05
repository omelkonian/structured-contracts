module Prelude where

open import Prelude.Init public
open SetAsType public
open L.Mem public
open import Prelude.Membership public using (_∈?_; _∉?_)
open import Prelude.Maybes public
open import Prelude.InferenceRules public
open import Prelude.Lists.Sums public
open import Prelude.General public
open import Prelude.Maybes public
open import Prelude.Decidable public
open import Prelude.DecEq public
open import Prelude.Maps public
open import Prelude.Semigroup public
open import Prelude.Monoid public
open import Prelude.Functor public
open import Prelude.Applicative public
open import Prelude.ToN public
open import Prelude.FromList public
open import Prelude.Lists hiding (_⁉_; _‼_; map↦)
open import Prelude.Lists.Dec public
open import Prelude.Lists.WithK public
open import Prelude.Irrelevance hiding (_─_) public
-- open import Prelude.Apartness public
open import Prelude.Ord public
-- open import Prelude.Membership public
open import Prelude.ToList public
open import Prelude.Bifunctor public

All-syntax = All
syntax All-syntax (λ i → P) xs = ∀[ i ∈ xs ] P

Any-syntax = Any
syntax Any-syntax (λ i → P) xs = ∃[ i ∈ xs ] P

-- ** Map utilities
module _ {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where
  open import Prelude.ToList

  private variable
    k k′ : K
    ks   : List K
    v v′ : V
    m m′ m″ : Map⟨ K ↦ V ⟩

  _‼_ : (m : Map⟨ K ↦ V ⟩) → k ∈ᵈ m → V
  m ‼ k∈ = destruct-Is-just (∈ᵈ⇒⁉ m k∈) .proj₁

  _─ᵏˢ_ : Map⟨ K ↦ V ⟩ → List K → Map⟨ K ↦ V ⟩
  m ─ᵏˢ ks = filterK (_∉? ks) m

  keys : Map⟨ K ↦ V ⟩ → List K
  keys = map proj₁ ∘ toList

  values : Map⟨ K ↦ V ⟩ → List V
  values = map proj₂ ∘ toList

  postulate
    -- * union properties
    ∅-identityˡ : ∅ ∪ m ≡ m
    ∅-identityʳ : m ∪ ∅ ≡ m
    ∪-reassoc   : m ∪ m′ ∪ m″ ≡ (m ∪ m″) ∪ m′
    -- * singleton properties
    singleton≢∅ : singleton (k , v) ≢ ∅
    -- * membership properties
    ∈ᵈ⁻    : k ∈ keys m → Σ V λ v → (k , v) ∈ toList m
    ∉ᵈ-∪   : k ∉ᵈ m → k ∉ᵈ m′ → k ∉ᵈ m ∪ m′
    ∉ᵈ-─ᵏˢ : k ∉ᵈ m → k ∉ᵈ (m ─ᵏˢ ks)
    ∈─⇒∉ᵈ  : k ∈ ks → k ∉ᵈ (m ─ᵏˢ ks)
    -- * filter properties
    filterK≢∅ : filterK (_≟ k) m ≢ ∅ → k ∈ᵈ m
    filter-∪ : ∀ {P : Pred₀ K} (P? : Decidable¹ P) {m m′ : Map⟨ K ↦ V ⟩} →
      filterK P? (m ∪ m′) ≡ filterK P? m ∪ filterK P? m′
  module _ ⦃ _ : Ord V ⦄ ⦃ _ : DecOrd V ⦄
           ⦃ _ : Semigroup V ⦄ ⦃ _ : Monoid V ⦄ where postulate
    -- * inclusion properties
    ⊆-∅    : m ≡ ∅  → m ≤ᵐ m′
    ⊆-refl : m ≡ m′ → m ≤ᵐ m′

-- ** Small-step relations
SSRel : Type → Type → Type → Type₁
SSRel Env State Input = Env → State → Input → State → Type

private variable
  Env Env′ S S′ I I′ : Type
  Γ Δ : Env
  s s′ : S
  i i′ : I

-- 𝔸 reifies/simulates/implements 𝔹
record _≼_ (𝔸 : SSRel Env S I) (𝔹 : SSRel Env′ S′ I′) : Type where
  field
    πₑ : Env → S → I → Env′
    πₛ : S → S′
    πᵢ : I → I′
    implements : ∀ Γ s i s′ → 𝔸 Γ s i s′ → 𝔹 (πₑ Γ s i) (πₛ s) (πᵢ i) (πₛ s′)
open _≼_ public

_≽_ _≋_ : SSRel Env S I → SSRel Env′ S′ I′ → Type
𝔹 ≽ 𝔸 = 𝔸 ≼ 𝔹 -- 𝔸 refines 𝔹
𝔸 ≋ 𝔹 = (𝔸 ≼ 𝔹) × (𝔸 ≽ 𝔹) -- 𝔸 is equivalent to 𝔹

-- alternative relational presentation
record _≼′_ (𝔸 : SSRel Env S I) (𝔹 : SSRel Env′ S′ I′) : Type₁ where
  field
    _~ˢ_ : S → S′ → Type
    _~ᵉ_ : Env × I → Env′ × I′ → Type
    implements′ : ∀ Γ Γ′ s u i i′ s′ →
      ∙ 𝔸 Γ s i s′
      ∙ (Γ , i) ~ᵉ (Γ′ , i′)
      ∙ s ~ˢ u
        ─────────────────────
        ∃ λ u′ → s′ ~ˢ u′
               × 𝔹 Γ′ u i′ u′
open _≼′_ public

_≽′_ _≋′_ : SSRel Env S I → SSRel Env′ S′ I′ → Type₁
𝔹 ≽′ 𝔸 = 𝔸 ≼′ 𝔹 -- 𝔸 refines 𝔹
𝔸 ≋′ 𝔹 = (𝔸 ≼′ 𝔹) × (𝔸 ≽′ 𝔹) -- 𝔸 is equivalent to 𝔹
