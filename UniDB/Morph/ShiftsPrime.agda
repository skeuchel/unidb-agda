
module UniDB.Morph.ShiftsPrime where

open import UniDB.Spec
open import UniDB.Basic
open import UniDB.Subst
open import Function
open import Data.Product

--------------------------------------------------------------------------------

mutual
  data Shifts* : MOR where
    refl : {γ : Dom} → Shifts* γ γ
    incl : {γ₁ γ₂ : Dom} (ξ : Shifts+ γ₁ γ₂) → Shifts* γ₁ γ₂

  data Shifts+ : MOR where
    step : {γ₁ γ₂ : Dom} (ξ : Shifts* γ₁ γ₂) → Shifts+ γ₁ (suc γ₂)
    skip : {γ₁ γ₂ : Dom} (ξ : Shifts+ γ₁ γ₂) → Shifts+ (suc γ₁) (suc γ₂)

mutual
  shiftIx* : {γ₁ γ₂ : Dom} (ξ : Shifts* γ₁ γ₂) (i : Ix γ₁) → Ix γ₂
  shiftIx* refl     i = i
  shiftIx* (incl ξ) i = shiftIx+ ξ i

  shiftIx+ : {γ₁ γ₂ : Dom} (ξ : Shifts+ γ₁ γ₂) (i : Ix γ₁) → Ix γ₂
  shiftIx+ (skip ξ) zero    = zero
  shiftIx+ (skip ξ) (suc i) = suc (shiftIx+ ξ i)
  shiftIx+ (step ξ) i       = suc (shiftIx* ξ i)

mutual
  _⊙**_ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) → Shifts* γ₁ γ₃
  ξ₁ ⊙** refl    = ξ₁
  ξ₁ ⊙** incl ξ₂ = incl (ξ₁ ⊙*+ ξ₂)

  _⊙*+_ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) → Shifts+ γ₁ γ₃
  refl    ⊙*+ ξ₂ = ξ₂
  incl ξ₁ ⊙*+ ξ₂ = ξ₁ ⊙++ ξ₂

  _⊙+*_ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) → Shifts+ γ₁ γ₃
  ξ₁ ⊙+* refl    = ξ₁
  ξ₁ ⊙+* incl ξ₂ = ξ₁ ⊙++ ξ₂

  _⊙++_ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) → Shifts+ γ₁ γ₃
  ξ₁      ⊙++ step ξ₂ = step (incl (ξ₁ ⊙+* ξ₂))
  step ξ₁ ⊙++ skip ξ₂ = step (incl (ξ₁ ⊙*+ ξ₂))
  skip ξ₁ ⊙++ skip ξ₂ = skip (ξ₁ ⊙++ ξ₂)

--------------------------------------------------------------------------------

instance
  iLkShifts* : {T : STX} {{vrT : Vr T}} → Lk T Shifts*
  lk {{iLkShifts*}} ξ i = vr {_} (shiftIx* ξ i)

  iLkShifts+ : {T : STX} {{vrT : Vr T}} → Lk T Shifts+
  lk {{iLkShifts+}} ξ i = vr {_} (shiftIx+ ξ i)

  iUpShifts* : Up Shifts*
  _↑₁ {{iUpShifts*}} refl     = refl
  _↑₁ {{iUpShifts*}} (incl ξ) = incl (skip ξ)
  _↑_ {{iUpShifts*}} ξ 0 = ξ
  _↑_ {{iUpShifts*}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpShifts*}} ξ = refl
  ↑-suc {{iUpShifts*}} ξ δ⁺ = refl

  iUpShifts+ : Up Shifts+
  _↑₁ {{iUpShifts+}} ξ = skip ξ
  _↑_ {{iUpShifts+}} ξ 0 = ξ
  _↑_ {{iUpShifts+}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpShifts+}} ξ = refl
  ↑-suc {{iUpShifts+}} ξ δ⁺ = refl

  iIdmShifts* : Idm Shifts*
  idm {{iIdmShifts*}} γ = refl {γ}

  iWkmShifts* : Wkm Shifts*
  wkm {{iWkmShifts*}} zero    = idm {Shifts*} _
  wkm {{iWkmShifts*}} (suc δ) = incl (step (wkm {Shifts*} δ))

  iCompShifts* : Comp Shifts*
  _⊙_ {{iCompShifts*}} = _⊙**_

  iCompShifts+ : Comp Shifts+
  _⊙_ {{iCompShifts+}} = _⊙++_

--------------------------------------------------------------------------------

suc-inj : {γ : Dom} {i j : Ix γ} → _≡_ {A = Ix (suc γ)} (suc i) (suc j) → i ≡ j
suc-inj refl = refl

shift₁≠id : {γ : Dom} (ξ : Shifts+ γ γ) →
  Σ[ i ∈ Ix γ ] shiftIx+ ξ i ≢ i
shift₁≠id (skip ξ) with shift₁≠id ξ
shift₁≠id (skip ξ) | w , ¬p = suc w , ¬p ∘ suc-inj
shift₁≠id (step ξ) = zero , λ ()

mutual
  extensionality-shifts* : {γ₁ γ₂ : Dom} (ξ₁ ξ₂ : Shifts* γ₁ γ₂)
    (hyp : (i : Ix γ₁) → lk {Ix} ξ₁ i ≡ lk {Ix} ξ₂ i) →
    ξ₁ ≡ ξ₂
  extensionality-shifts* refl      refl      hyp = refl
  extensionality-shifts* refl      (incl ξ₂) hyp with shift₁≠id ξ₂
  ... | w , ¬p = case ¬p (sym (hyp w)) of λ()
  extensionality-shifts* (incl ξ₁) refl      hyp with shift₁≠id ξ₁
  ... | w , ¬p = case ¬p (hyp w) of λ()
  extensionality-shifts* (incl ξ₁) (incl ξ₂) hyp = cong incl (extensionality-shifts+ ξ₁ ξ₂ hyp)

  extensionality-shifts+ : {γ₁ γ₂ : Dom} (ξ₁ ξ₂ : Shifts+ γ₁ γ₂)
    (hyp : (i : Ix γ₁) → lk {Ix} ξ₁ i ≡ lk {Ix} ξ₂ i) →
    ξ₁ ≡ ξ₂
  extensionality-shifts+ (skip ξ₁) (skip ξ₂) hyp = cong skip (extensionality-shifts+ ξ₁ ξ₂ (suc-inj ∘ hyp ∘ suc))
  extensionality-shifts+ (skip ξ₁) (step ξ₂) hyp = case hyp zero of λ()
  extensionality-shifts+ (step ξ₁) (skip ξ₂) hyp = case hyp zero of λ()
  extensionality-shifts+ (step ξ₁) (step ξ₂) hyp = cong step (extensionality-shifts* ξ₁ ξ₂ (suc-inj ∘ hyp))

mutual
  shiftIx-⊙** : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) →
    (i : Ix γ₁) → shiftIx* (ξ₁ ⊙** ξ₂) i ≡ shiftIx* ξ₂ (shiftIx* ξ₁ i)
  shiftIx-⊙** ξ₁ refl      i = refl
  shiftIx-⊙** ξ₁ (incl ξ₂) i = shiftIx-⊙*+ ξ₁ ξ₂ i

  shiftIx-⊙*+ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) →
    (i : Ix γ₁) → shiftIx+ (ξ₁ ⊙*+ ξ₂) i ≡ shiftIx+ ξ₂ (shiftIx* ξ₁ i)
  shiftIx-⊙*+ refl      ξ₂ i = refl
  shiftIx-⊙*+ (incl ξ₁) ξ₂ i = shiftIx-⊙++ ξ₁ ξ₂ i

  shiftIx-⊙+* : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) →
    (i : Ix γ₁) → shiftIx+ (ξ₁ ⊙+* ξ₂) i ≡ shiftIx* ξ₂ (shiftIx+ ξ₁ i)
  shiftIx-⊙+* ξ₁ refl      i = refl
  shiftIx-⊙+* ξ₁ (incl ξ₂) i = shiftIx-⊙++ ξ₁ ξ₂ i

  shiftIx-⊙++ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) →
    (i : Ix γ₁) → shiftIx+ (ξ₁ ⊙++ ξ₂) i ≡ shiftIx+ ξ₂ (shiftIx+ ξ₁ i)
  shiftIx-⊙++ ξ₁        (step ξ₂) i       = cong suc (shiftIx-⊙+* ξ₁ ξ₂ i)
  shiftIx-⊙++ (step ξ₁) (skip ξ₂) i       = cong suc (shiftIx-⊙*+ ξ₁ ξ₂ i)
  shiftIx-⊙++ (skip ξ₁) (skip ξ₂) zero    = refl
  shiftIx-⊙++ (skip ξ₁) (skip ξ₂) (suc i) = cong suc (shiftIx-⊙++ ξ₁ ξ₂ i)

⊙**-↑₁ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) →
  (ξ₁ ⊙** ξ₂) ↑₁ ≡ (ξ₁ ↑₁) ⊙** (ξ₂ ↑₁)
⊙**-↑₁ ξ₁        refl      = refl
⊙**-↑₁ refl      (incl ξ₂) = refl
⊙**-↑₁ (incl ξ₁) (incl ξ₂) = refl

⊙++-↑₁ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) →
  (ξ₁ ⊙++ ξ₂) ↑₁ ≡ (ξ₁ ↑₁) ⊙++ (ξ₂ ↑₁)
⊙++-↑₁ ξ₁        (step ξ₂) = refl
⊙++-↑₁ (step ξ₁) (skip ξ₂) = refl
⊙++-↑₁ (skip ξ₁) (skip ξ₂) = refl

mutual
  ⊙***-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) (ξ₃ : Shifts* γ₃ γ₄) →
    (ξ₁ ⊙** (ξ₂ ⊙** ξ₃)) ≡ ((ξ₁ ⊙** ξ₂) ⊙** ξ₃)
  ⊙***-assoc ξ₁ ξ₂ refl      = refl
  ⊙***-assoc ξ₁ ξ₂ (incl ξ₃) = cong incl (⊙**+-assoc ξ₁ ξ₂ ξ₃)

  ⊙**+-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) (ξ₃ : Shifts+ γ₃ γ₄) →
    (ξ₁ ⊙*+ (ξ₂ ⊙*+ ξ₃)) ≡ ((ξ₁ ⊙** ξ₂) ⊙*+ ξ₃)
  ⊙**+-assoc ξ₁ refl      ξ₃ = refl
  ⊙**+-assoc ξ₁ (incl ξ₂) ξ₃ = ⊙*++-assoc ξ₁ ξ₂ ξ₃

  ⊙*++-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts* γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) (ξ₃ : Shifts+ γ₃ γ₄) →
    (ξ₁ ⊙*+ (ξ₂ ⊙++ ξ₃)) ≡ ((ξ₁ ⊙*+ ξ₂) ⊙++ ξ₃)
  ⊙*++-assoc refl      ξ₂ ξ₃ = refl
  ⊙*++-assoc (incl ξ₁) ξ₂ ξ₃ = ⊙+++-assoc ξ₁ ξ₂ ξ₃

  ⊙++*-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) (ξ₃ : Shifts* γ₃ γ₄) →
    (ξ₁ ⊙++ (ξ₂ ⊙+* ξ₃)) ≡ ((ξ₁ ⊙++ ξ₂) ⊙+* ξ₃)
  ⊙++*-assoc ξ₁ ξ₂ refl      = refl
  ⊙++*-assoc ξ₁ ξ₂ (incl ξ₃) = ⊙+++-assoc ξ₁ ξ₂ ξ₃

  ⊙+*+-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts* γ₂ γ₃) (ξ₃ : Shifts+ γ₃ γ₄) →
    (ξ₁ ⊙++ (ξ₂ ⊙*+ ξ₃)) ≡ ((ξ₁ ⊙+* ξ₂) ⊙++ ξ₃)
  ⊙+*+-assoc ξ₁ refl      ξ₃ = refl
  ⊙+*+-assoc ξ₁ (incl ξ₂) ξ₃ = ⊙+++-assoc ξ₁ ξ₂ ξ₃

  ⊙+++-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Shifts+ γ₁ γ₂) (ξ₂ : Shifts+ γ₂ γ₃) (ξ₃ : Shifts+ γ₃ γ₄) →
    (ξ₁ ⊙++ (ξ₂ ⊙++ ξ₃)) ≡ ((ξ₁ ⊙++ ξ₂) ⊙++ ξ₃)
  ⊙+++-assoc ξ₁        ξ₂        (step ξ₃) = cong (step ∘ incl) (⊙++*-assoc ξ₁ ξ₂ ξ₃)
  ⊙+++-assoc ξ₁        (step ξ₂) (skip ξ₃) = cong (step ∘ incl) (⊙+*+-assoc ξ₁ ξ₂ ξ₃)
  ⊙+++-assoc (step ξ₁) (skip ξ₂) (skip ξ₃) = cong (step ∘ incl) (⊙*++-assoc ξ₁ ξ₂ ξ₃)
  ⊙+++-assoc (skip ξ₁) (skip ξ₂) (skip ξ₃) = cong skip (⊙+++-assoc ξ₁ ξ₂ ξ₃)

--------------------------------------------------------------------------------

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkUpShifts* : {{wkT : Wk T}} {{wkVrT : WkVr T}} → LkUp T Shifts*
    lk-↑₁-zero {{iLkUpShifts*}} refl       = refl
    lk-↑₁-zero {{iLkUpShifts*}} (incl ξ)   = refl
    lk-↑₁-suc  {{iLkUpShifts*}} refl i     = sym (wk₁-vr {T} i)
    lk-↑₁-suc  {{iLkUpShifts*}} (incl ξ) i = sym (wk₁-vr {T} (shiftIx+ ξ i))

    iLkRenShifts* : LkRen T Shifts*
    lk-ren {{iLkRenShifts*}} ξ i = refl

    iLkIdmShifts* : LkIdm T Shifts*
    lk-idm {{iLkIdmShifts*}} i = refl

    iLkWkmShifts* : LkWkm T Shifts*
    lk-wkm {{iLkWkmShifts*}} δ i = cong vr (lem δ i)
      where
        lem : {γ : Dom} (δ : Dom) (i : Ix γ) →
          shiftIx* (wkm {Shifts*} δ) i ≡ wk {Ix} δ i
        lem zero i = refl
        lem (suc δ) i = cong suc (lem δ i)

    iLkCompApShifts* : {{apTT : Ap T T}} {{apVrT : ApVr T}} → LkCompAp T Shifts*
    lk-⊙-ap {{iLkCompApShifts*}} {Ξ} ξ₁ ξ₂ i = begin
      vr (lk {Ix} (ξ₁ ⊙ ξ₂) i)     ≡⟨ cong vr (shiftIx-⊙** ξ₁ ξ₂ i) ⟩
      lk {T} ξ₂ (lk {Ix} ξ₁ i)      ≡⟨ sym (ap-vr {T} ξ₂ (lk ξ₁ i)) ⟩
      ap {T} ξ₂ (vr (lk {Ix} ξ₁ i)) ∎ -- sym {!ap-vr {T} !}

instance
  iUpIdmShifts* : UpIdm Shifts*
  idm-↑₁ {{iUpIdmShifts*}} = refl

  iCompIdmShifts* : CompIdm Shifts*
  ⊙-idm {{iCompIdmShifts*}} ξ        = refl
  idm-⊙ {{iCompIdmShifts*}} refl     = refl
  idm-⊙ {{iCompIdmShifts*}} (incl ξ) = refl

  iUpCompShifts* : UpComp Shifts*
  ⊙-↑₁ {{iUpCompShifts*}} ξ₁ ξ₂ = ⊙**-↑₁ ξ₁ ξ₂
    -- extensionality-shifts* ((ξ₁ ⊙ ξ₂) ↑₁) (ξ₁ ↑₁ ⊙ ξ₂ ↑₁)
    --   (lk≃ {Ix} {Shifts*} {ξ = (ξ₁ ⊙ ξ₂) ↑₁} {ξ₁ ↑₁ ⊙ ξ₂ ↑₁}
    --   (⊙-↑₁-pointwise {Ix} {{apWkTT =  iApWk Ix Ix}} {Shifts*} ξ₁ ξ₂))

  iCompAssoc* : CompAssoc Shifts*
  ⊙-assoc {{iCompAssoc*}} = ⊙***-assoc

  iUpCompShifts+ : UpComp Shifts+
  ⊙-↑₁ {{iUpCompShifts+}} = ⊙++-↑₁

  iCompAssoc+ : CompAssoc Shifts+
  ⊙-assoc {{iCompAssoc+}} = ⊙+++-assoc

--------------------------------------------------------------------------------

{-
  iWkmHomShifts* : WkmHom Shifts*
  wkm-zero {{iWkmHomShifts*}}   = {!!}
  wkm-suc  {{iWkmHomShifts*}} δ = {!!}
-}
