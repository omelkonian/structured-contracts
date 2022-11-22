open import Prelude.Init hiding (id); open SetAsType
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Maps

-- small-step relations
SSRel : Type × Type × Type → Type₁
SSRel (Env , State , Input) = Env → State → Input → State → Type

-- ** Ledger

postulate
  LEnv LState Tx : Type
  _⊢_—⟨_∣UTXOW⟩→_ : SSRel (LEnv , LState , Tx)

variable
  env : LEnv
  utxoSt utxoSt′ : LState
  tx : Tx

data _⊢_—⟨_∣LEDGER⟩→_ : SSRel (LEnv , LState , Tx) where

  ledger-V :
    env ⊢ utxoSt —⟨ tx ∣UTXOW⟩→ utxoSt′
    ────────────────────────────────────
    env ⊢ utxoSt —⟨ tx ∣LEDGER⟩→ utxoSt′

-- ** Simulation

postulate
  TxInfo : Type
  getUTxO : LState → Tx → TxInfo
  isValid : Tx → Bool

variable
  txInfo : TxInfo

module Simulation
  {State Input : Type}
  ⦃ _ : Monoid Input ⦄
  (πˢ : LState → State)
  (πⁱ : TxInfo → Input)
  (_⊢_—⟨_∣SMUP⟩→_ : SSRel (TxInfo , State , Input))
  where

  data StatefulStep : Type where
    STEP :
      (let txInfo = getUTxO utxoSt tx in
      ∙ T (isValid tx)
      ∙ πⁱ txInfo ≢ ε
      ∙ env ⊢ utxoSt —⟨ tx ∣LEDGER⟩→ utxoSt′
        ───────────────────────────────────────────────────
        txInfo ⊢ πˢ utxoSt —⟨ πⁱ txInfo ∣SMUP⟩→ πˢ utxoSt′)
      ────────────
      StatefulStep

  data StatefulNoStep : Type where
    NO-STEP :
      (let txInfo = getUTxO utxoSt tx in
      ∙ T (isValid tx)
      ∙ πⁱ txInfo ≡ ε
      ∙ env ⊢ utxoSt —⟨ tx ∣LEDGER⟩→ utxoSt′
        ────────────────────────────────────
        πˢ utxoSt ≡ πˢ utxoSt′)
      ──────────────
      StatefulNoStep

IsSimulation : ∀ {S I : Type} → ⦃ Monoid I ⦄ → Pred₀ (SSRel (TxInfo , S , I))
IsSimulation {S}{I} ssRel =
  ∃ λ (πˢ : LState → S) → ∃ λ (πⁱ : TxInfo → I) →
  let open Simulation πˢ πⁱ ssRel in
    Surjective≡ {A = LState} πˢ
  × Surjective≡ {A = TxInfo} πⁱ
  × StatefulStep
  × StatefulNoStep

-- ** NFT state machine library

postulate
  SMS SMI Value : Type
  instance _ : Monoid SMS
           _ : Monoid Value
           _ : Monoid SMI
  initState : SMS × Value
  SpendsNFT PutsNFT PropagatesNFT : Pred₀ TxInfo
  buildConstraints : TxInfo → List (SMS → SMI → Bool)
  _⊢_—⟨_∣SMPEC⟩→_ : SSRel (TxInfo , (SMS × Value) , SMI)

variable
  sms sms′ : SMS
  smi : SMI
  val val′ : Value

data _⊢_—⟨_∣NFTCE⟩→_ : SSRel (TxInfo , (SMS × Value) , SMI) where

  MintsNFT :
    ∙ SpendsNFT txInfo
    ∙ PutsNFT txInfo
    ∙ env ⊢ utxoSt —⟨ tx ∣UTXOW⟩→ utxoSt′
      ────────────────────────────────────
      txInfo ⊢ ε —⟨ smi ∣NFTCE⟩→ initState

  PropogatesNFT :
    ∙ All (λ P → T $ P sms smi) (buildConstraints txInfo)
    ∙ PropagatesNFT txInfo
    ∙ txInfo ⊢ (sms , val) —⟨ smi ∣SMPEC⟩→ (sms′ , val′)
      ──────────────────────────────────────────────────
      txInfo ⊢ (sms , val) —⟨ smi ∣NFTCE⟩→ (sms′ , val′)

postulate LEDGER-simulates-NFTCE : IsSimulation _⊢_—⟨_∣NFTCE⟩→_

-- ** Account simulation

data IType : Type where
  OArgs CArgs : IType
unquoteDecl Derive-IType = DERIVE DecEq [ quote IType , Derive-IType ]

postulate
  Id Key : Type
  instance _ : DecEq Id
           _ : DecEq Key
           _ : DecEq Value

record AccI : Type where
  field id : Id
        pk : Key
open AccI

record Account : Type where
  field id : Id
        value : Value
        pk : Key
open Account
unquoteDecl Derive-Account = DERIVE DecEq [ quote Account , Derive-Account ]

postulate
  instance _ : Monoid AccI
  txInfoSignatories : TxInfo → List Key
  itype : AccI → IType

variable
  accIn : AccI
  accts : Map⟨ Id ↦ Account ⟩
  newAcct acntToClose : Account

data _⊢_—⟨_∣ACCNT⟩→_ : SSRel (TxInfo , Map⟨ Id ↦ Account ⟩ , AccI) where

  Open :

    ∙ itype accIn ≡ OArgs
    ∙ accIn .pk ∈ txInfoSignatories txInfo
    ∙ accIn .id ∉ᵈ accts
    ∙ newAcct .pk ≡ accIn .pk
    ∙ newAcct .value ≡ ε
      ──────────────────────────────────────────────────────────────────────────
      txInfo ⊢ accts —⟨ accIn ∣ACCNT⟩→ (accts ∪ singleton (accIn .id , newAcct))

  Close :

    ∙ itype accIn ≡ CArgs
    ∙ accts [ accIn .id ↦ acntToClose ]
    ∙ accIn .pk ∈ txInfoSignatories txInfo
    ∙ acntToClose .value ≡ ε
      ────────────────────────────────────────────────────
      txInfo ⊢ accts —⟨ accIn ∣ACCNT⟩→ (accIn .id ⋪ accts)

postulate LEDGER-simulates-ACCNT : IsSimulation _⊢_—⟨_∣ACCNT⟩→_
