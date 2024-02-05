module NFT where

open import Prelude
open import EUTxO
open import Struc

oneT : PolicyID → TokenName → Value
oneT pid tk = singleton (pid , singleton (tk , 1))

-- assume unspent origin for non-fungibility
postulate myNFTRef : TxOutputRef

myNFTToken : TokenName
myNFTToken = 42

myNFTPolicyScript : MintingPolicy
myNFTPolicyScript (txi , pid) _
  = ⌊ ¿ (myNFTRef ∈ (InputInfo.outputRef <$> txi .TxInfo.inputs))
      × (filterK (_≟ pid) (txi .TxInfo.mint) ≡ oneT pid myNFTToken) ¿ ⌋

myNFTPolicy : Hash
myNFTPolicy = myNFTPolicyScript ♯

myOneNFT : Value
myOneNFT = oneT myNFTPolicy myNFTToken

filterNFT : Op₁ Value
filterNFT = filterK (_≟ myNFTPolicy)

data _⊢_—⟨_∣NFT⟩→_ : SSRel ⊤ Value Tx where
  UpdateNFTTotal :
    let
      i : Value
      i  = filterNFT (tx .mint)
      v′ : Value
      v′ = v ∪ i
    in

    v′ ≤ᵐ myOneNFT
    ───────────────────────────────────────────
    _ ⊢ v —⟨ tx ∣NFT⟩→ v′

_ : StrucSimulation Value Tx _⊢_—⟨_∣NFT⟩→_
_ = record { πˢ = π ; πⁱ = id ; simulates = sim }
  where
  open ≡-Reasoning

  -- * state projection
  π : UTxO → Maybe Value
  π utxos = let s = filterNFT (∑ᵐ utxos) in
    if ⌊ ¿ ((s ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos)) ⊎ (s ≡ ∅) ¿ ⌋ then
      just s
    else
      nothing

  -- Assume reminting protection
  postulate
    remintingProtection :
      ∙ slot ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′
      ∙ (π utxos ≡ just myOneNFT) ⊎ (myNFTRef ∈ outputRefs tx)
        ──────────────────────────────────────────────────────
        tx ♯ ≢ myNFTRef .txId

  -- * lemmas about state projection
  π-ok : let s = filterNFT (∑ᵐ utxos) in
    ((s ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos)) ⊎ (s ≡ ∅)
    ═══════════════════════════════════════════════════
    π utxos ≡ just s
  π-ok {utxos} = ↝ , ↜
    where
    s  = filterNFT (∑ᵐ utxos)
    Ps = ((s ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos)) ⊎ (s ≡ ∅)

    ↝ : Ps → π utxos ≡ just s
    ↝ p with ¿ Ps ¿
    ... | no ¬p = ⊥-elim $ ¬p p
    ... | yes _ = if-true {b = ⌊ ¿ Ps ¿ ⌋} $ T⇒true $ fromWitness {Q = ¿ Ps ¿} p

    ↜ : π utxos ≡ just s → Ps
    ↜ π≡ with ¿ Ps ¿ | π≡
    ... | yes p | _ = p

  π≡just :
    π utxos ≡ just v
    ───────────────────────
    v ≡ filterNFT (∑ᵐ utxos)
  π≡just {utxos} π≡
    with ¿ (let s = filterNFT (∑ᵐ utxos) in
          ((s ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos)) ⊎ (s ≡ ∅)) ¿ | π≡
  ... | yes _ | just≡ = sym $ M.just-injective just≡

  -- * simulation proof
  sim : ∀ slot Γ utxos v tx tx′ utxos′ →
    ∙ slot ⊢ utxos —⟨ tx ∣LEDGER⟩→ utxos′
    ∙ id tx ≡ tx′
    ∙ π utxos ≡ just v
      ─────────────────────────────────
      ∃ λ v′ → (π utxos′ ≡ just v′)
            × (Γ ⊢ v —⟨ tx′ ∣NFT⟩→ v′)
  sim slot _ utxos v tx .tx utxos′@(.(applyTx tx utxos))
      LEDGER→@(ApplyTx check≡) refl π≡
    with refl ← π≡just {utxos = utxos} π≡
    = s′ , bimap (π-ok {utxos′} .proj₁) mkNFT→ QED
    where
    i s s′ : Value
    i  = filterNFT (tx .mint)
    s  = filterNFT (∑ᵐ utxos)
    s′ = filterNFT (∑ᵐ utxos′)

    valid : IsValidTx slot tx utxos
    valid = toWitness check≡

    s′≡s∪i : s′ ≡ s ∪ i
    s′≡s∪i =
      begin
        s′
      ≡⟨⟩
        filterNFT (∑ᵐ utxos′)
      ≡⟨⟩
        filterNFT (∑ᵐ $ applyTx tx utxos)
      ≡⟨⟩
        filterNFT (∑ᵐ $ (utxos ─ᵏˢ outputRefs tx) ∪ utxoTx tx)
      ≡⟨ cong filterNFT $ ∑ᵐ-∪ {utxos ─ᵏˢ outputRefs tx}{utxoTx tx} ⟩
        filterNFT (∑utxos─ ∪ ∑ᵐ (utxoTx tx))
      ≡⟨ filter-∪ (_≟ myNFTPolicy) {∑utxos─}{∑ᵐ (utxoTx tx)} ⟩
        filterNFT ∑utxos─ ∪ filterNFT (∑ᵐ $ utxoTx tx)
      ≡⟨ cong (λ ◆ → filterNFT ∑utxos─ ∪ filterNFT ◆) (∑utxoTx≡ valid) ⟩
        filterNFT ∑utxos─ ∪ filterNFT (tx .mint ∪ ∑rins)
      ≡⟨ cong (filterNFT ∑utxos─ ∪_) $ filter-∪ (_≟ myNFTPolicy) {tx .mint}{∑rins} ⟩
        filterNFT ∑utxos─ ∪ filterNFT (tx .mint) ∪ filterNFT ∑rins
      ≡⟨ ∪-reassoc {m = filterNFT ∑utxos─}{filterNFT (tx .mint)}{filterNFT ∑rins} ⟩
        (filterNFT ∑utxos─ ∪ filterNFT ∑rins) ∪ filterNFT (tx .mint)
      ≡˘⟨ cong (_∪ filterNFT (tx .mint)) (filter-∪ (_≟ myNFTPolicy) {∑utxos─}{∑rins}) ⟩
        filterNFT (∑utxos─ ∪ ∑rins) ∪ filterNFT (tx .mint)
      ≡⟨ cong (_∪ filterNFT (tx .mint)) $ cong filterNFT (∑utxos─∪≡ valid) ⟩
        filterNFT (∑ᵐ utxos) ∪ filterNFT (tx .mint)
      ≡⟨⟩
        s ∪ i
      ∎ where ∑rins   = ∑ (value ∘ proj₂ <$> resolvedInputs valid)
              ∑utxos─ = ∑ᵐ (utxos ─ᵏˢ outputRefs tx)

    mkNFT→ : s′ ≤ᵐ myOneNFT → (_ ⊢ s —⟨ tx ∣NFT⟩→ s′)
    mkNFT→ p = subst (_ ⊢ s —⟨ tx ∣NFT⟩→_) (sym s′≡s∪i)
            $ UpdateNFTTotal
            $ subst (_≤ᵐ myOneNFT) s′≡s∪i p

    QED : ( ((s′ ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos′))
          ⊎ (s′ ≡ ∅) )
        × (s′ ≤ᵐ myOneNFT)
    QED =
      case i ≟ ∅ of λ where
      (yes i≡∅) →
        let
          s≡s′ : s ≡ s′
          s≡s′ = sym $ begin
            s′    ≡⟨ s′≡s∪i ⟩
            s ∪ i ≡⟨ cong (s ∪_) i≡∅ ⟩
            s ∪ ∅ ≡⟨ ∅-identityʳ ⟩
            s     ∎
        in
        case s ≟ ∅ of λ where
        (yes s≡∅) →
          let
            s′≡∅ : s′ ≡ ∅
            s′≡∅ = subst (_≡ ∅) s≡s′ s≡∅
          in
            inj₂ s′≡∅ , ⊆-∅ {m′ = myOneNFT} s′≡∅
        (no s≢∅) →
          let
            Ps : ((s ≡ myOneNFT) × (myNFTRef ∉ᵈ utxos))
                ⊎ (s ≡ ∅)
            Ps = π-ok {utxos = utxos} .proj₂ π≡

            s≡𝟙 : s ≡ myOneNFT
            s≡𝟙 = case Ps of λ where
              (inj₁ (s≡𝟙 , _)) → s≡𝟙
              (inj₂ s≡∅)       → ⊥-elim $ s≢∅ s≡∅

            ∉utxo : myNFTRef ∉ᵈ utxos
            ∉utxo = case Ps of λ where
              (inj₁ (_ , p)) → p
              (inj₂ s≡∅)     → ⊥-elim $ s≢∅ s≡∅

            s′≡𝟙 : s′ ≡ myOneNFT
            s′≡𝟙 = subst (_≡ myOneNFT) s≡s′ s≡𝟙

            π≡𝟙 : π utxos ≡ just myOneNFT
            π≡𝟙 = subst (λ ◆ → π utxos ≡ just ◆) s≡𝟙 π≡

            ∉utxo′ : myNFTRef ∉ᵈ utxos′
            ∉utxo′ = ∉ᵈ-∪ {m = utxos ─ᵏˢ outputRefs tx}{utxoTx tx}
              (∉ᵈ-─ᵏˢ {m = utxos} ∉utxo)
              (∉utxoTx $ remintingProtection LEDGER→ (inj₁ π≡𝟙))
          in
            inj₁ (s′≡𝟙 , ∉utxo′) , ⊆-refl s′≡𝟙
      (no i≢∅) →
        let
          txi : TxInfo
          txi = txInfo valid

          apv : ∀[ (p , r) ∈ toList (tx .mintRdrs) ]
                  T (p (txi , p ♯) r)
          apv = valid .allPoliciesValidate

          nft∈ : myNFTPolicy ∈ᵈ tx .mint
          nft∈ = filterK≢∅ {m = tx .mint} i≢∅

          nft∈′ : myNFTPolicy ∈ map _♯ (keys (tx .mintRdrs))
          nft∈′ = valid .validMintRedeemers nft∈

          nft∈″ : myNFTPolicyScript ∈ᵈ tx .mintRdrs
          nft∈″ =
            let f , f∈ , f≡ = L.Mem.∈-map⁻ _♯ nft∈′
            in subst (_∈ᵈ tx .mintRdrs) (sym $ ♯-injective f≡) f∈

          ∃kv : ∃ λ r → (myNFTPolicyScript , r) ∈ toList (tx .mintRdrs)
          ∃kv = ∈ᵈ⁻ {m = tx .mintRdrs} nft∈″

          rdm : Redeemer
          rdm = ∃kv .proj₁

          policy≡ : T (myNFTPolicyScript (txi , myNFTPolicy) rdm)
          policy≡ = L.All.lookup (valid .allPoliciesValidate) (∃kv .proj₂)

          ∈txins : myNFTRef ∈ outputRefs tx
          ∈txins = subst (_ ∈_) (outRefs≡ valid) (toWitness policy≡ .proj₁)

          ∈utxo : myNFTRef ∈ᵈ utxos
          ∈utxo = L.All.lookup (valid .validOutputRefs) ∈txins

          i≡𝟙 : i ≡ myOneNFT
          i≡𝟙 = toWitness policy≡ .proj₂
        in
        case s ≟ ∅ of λ where
        (yes s≡∅) →
          let
            s′≡𝟙 : s′ ≡ myOneNFT
            s′≡𝟙 = begin
              s′       ≡⟨ s′≡s∪i ⟩
              s ∪ i    ≡⟨ cong (_∪ i) s≡∅ ⟩
              ∅ ∪ i    ≡⟨ ∅-identityˡ ⟩
              i        ≡⟨ i≡𝟙 ⟩
              myOneNFT ∎

            ∉utxo′ : myNFTRef ∉ᵈ utxos′
            ∉utxo′ = ∉ᵈ-∪ {m = utxos ─ᵏˢ outputRefs tx}{utxoTx tx}
              (∈─⇒∉ᵈ {m = utxos} ∈txins)
              (∉utxoTx $ remintingProtection LEDGER→ (inj₂ ∈txins))
          in
            inj₁ (s′≡𝟙 , ∉utxo′) , ⊆-refl s′≡𝟙
        (no s≢∅) →
          let
            ∉utxo : myNFTRef ∉ᵈ utxos
            ∉utxo = case π-ok {utxos} .proj₂ π≡ of λ where
              (inj₁ (_ , ∉utxo)) → ∉utxo
              (inj₂ s≡∅)         → ⊥-elim $ s≢∅ s≡∅
          in
            ⊥-elim $ ∉utxo ∈utxo
