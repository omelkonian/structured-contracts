module NFT where

open import Prelude
open import Prelude.Ord
open import EUTxO

instance
  _ = Semigroup-ℕ-+
  _ = Monoid-ℕ-+

private variable tks : Map⟨ TokenName ↦ Quantity ⟩

postulate myNFTPolicy : Hash

data _⊢_—⟨_∣NFT⟩→_ : SSRel ⊤ Value Tx where
  UpdateNFTTotal :
    let
      i  = singleton (myNFTPolicy , tks)
      v′ = v ∪ i
    in

    tks ≤ᵐ fromMaybe ∅ (tx .mint ⁉ myNFTPolicy)
    ───────────────────────────────────────────
    _ ⊢ v —⟨ tx ∣NFT⟩→ v
