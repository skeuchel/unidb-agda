
module UniDB.Morph.Shifts where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Shifts : MOR where
  refl : {γ : Dom} → Shifts γ γ
  step : {γ₁ γ₂ : Dom} (ξ : Shifts γ₁ γ₂) → Shifts γ₁ (suc γ₂)
  skip : {γ₁ γ₂ : Dom} (ξ : Shifts γ₁ γ₂) → Shifts (suc γ₁) (suc γ₂)

shiftIx : {γ₁ γ₂ : Dom} (ξ : Shifts γ₁ γ₂) (i : Ix γ₁) → Ix γ₂
shiftIx refl     i       = i
shiftIx (step ξ) i       = suc (shiftIx ξ i)
shiftIx (skip ξ) zero    = zero
shiftIx (skip ξ) (suc i) = suc (shiftIx ξ i)

--------------------------------------------------------------------------------

instance
  iLkShifts : {T : STX} {{vrT : Vr T}} → Lk T Shifts
  lk {{iLkShifts}} ξ i = vr (shiftIx ξ i)

  iUpShifts : Up Shifts
  _↑₁    {{iUpShifts}} refl = refl
  _↑₁    {{iUpShifts}} ξ          = skip ξ
  _↑_    {{iUpShifts}} ξ 0        = ξ
  _↑_    {{iUpShifts}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpShifts}} ξ          = refl
  ↑-suc  {{iUpShifts}} ξ δ⁺       = refl

  iIdmShifts : Idm Shifts
  idm {{iIdmShifts}} γ = refl {γ}

  iWkmShifts : Wkm Shifts
  wkm {{iWkmShifts}} zero    = idm _
  wkm {{iWkmShifts}} (suc δ) = step (wkm δ)

  iCompShifts : Comp Shifts
  _⊙_ {{iCompShifts}} ξ₁        refl      = ξ₁
  _⊙_ {{iCompShifts}} ξ₁        (step ξ₂) = step (ξ₁ ⊙ ξ₂)
  _⊙_ {{iCompShifts}} refl      (skip ξ₂) = skip ξ₂
  _⊙_ {{iCompShifts}} (step ξ₁) (skip ξ₂) = step (ξ₁ ⊙ ξ₂)
  _⊙_ {{iCompShifts}} (skip ξ₁) (skip ξ₂) = skip (ξ₁ ⊙ ξ₂)

--------------------------------------------------------------------------------

shiftIx-⊙ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Shifts γ₁ γ₂) (ξ₂ : Shifts γ₂ γ₃) →
  (i : Ix γ₁) → shiftIx (ξ₁ ⊙ ξ₂) i ≡ shiftIx ξ₂ (shiftIx ξ₁ i)
shiftIx-⊙ ξ₁        refl      i       = refl
shiftIx-⊙ ξ₁        (step ξ₂) i       = cong suc (shiftIx-⊙ ξ₁ ξ₂ i)
shiftIx-⊙ refl      (skip ξ₂) i       = refl
shiftIx-⊙ (step ξ₁) (skip ξ₂) i       = cong suc (shiftIx-⊙ ξ₁ ξ₂ i)
shiftIx-⊙ (skip ξ₁) (skip ξ₂) zero    = refl
shiftIx-⊙ (skip ξ₁) (skip ξ₂) (suc i) = cong suc (shiftIx-⊙ ξ₁ ξ₂ i)

shiftIx-wkm : {γ : Dom} (δ : Dom) (i : Ix γ) →
  shiftIx (wkm δ) i ≡ wk δ i
shiftIx-wkm zero    i = refl
shiftIx-wkm (suc δ) i = cong suc (shiftIx-wkm δ i)

--------------------------------------------------------------------------------

instance
  iUpIdmShifts : UpIdm Shifts
  idm-↑₁ {{iUpIdmShifts}} = refl

  iCompIdmShifts : CompIdm Shifts
  ⊙-idm {{iCompIdmShifts}} ξ        = refl
  idm-⊙ {{iCompIdmShifts}} refl     = refl
  idm-⊙ {{iCompIdmShifts}} (step ξ) = cong step (idm-⊙ ξ)
  idm-⊙ {{iCompIdmShifts}} (skip ξ) = refl

  iUpCompShifts : UpComp Shifts
  ⊙-↑₁ {{iUpCompShifts}} ξ        refl     = refl
  ⊙-↑₁ {{iUpCompShifts}} refl     (step ζ) = cong (skip ∘ step) (idm-⊙ ζ)
  ⊙-↑₁ {{iUpCompShifts}} (step ξ) (step ζ) = refl
  ⊙-↑₁ {{iUpCompShifts}} (skip ξ) (step ζ) = refl
  ⊙-↑₁ {{iUpCompShifts}} refl     (skip ζ) = refl
  ⊙-↑₁ {{iUpCompShifts}} (step ξ) (skip ζ) = refl
  ⊙-↑₁ {{iUpCompShifts}} (skip ξ) (skip ζ) = refl

  iWkmHomShifts : WkmHom Shifts
  wkm-zero {{iWkmHomShifts}}   = refl
  wkm-suc  {{iWkmHomShifts}} δ = refl

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkUpShifts : {{wkT : Wk T}} {{wkVrT : WkVr T}} → LkUp T Shifts
    lk-↑₁-zero {{iLkUpShifts}} refl       = refl
    lk-↑₁-zero {{iLkUpShifts}} (step ξ)   = refl
    lk-↑₁-zero {{iLkUpShifts}} (skip ξ)   = refl
    lk-↑₁-suc  {{iLkUpShifts}} refl i     = sym (wk₁-vr i)
    lk-↑₁-suc  {{iLkUpShifts}} (step ξ) i = sym (wk₁-vr (suc (shiftIx ξ i)))
    lk-↑₁-suc  {{iLkUpShifts}} (skip ξ) i = sym (wk₁-vr (shiftIx (skip ξ) i))

    iLkRenShifts : LkRen T Shifts
    lk-ren {{iLkRenShifts}} ξ i = refl

    iLkIdmShifts : LkIdm T Shifts
    lk-idm {{iLkIdmShifts}} i = refl

    iLkWkmShifts : LkWkm T Shifts
    lk-wkm {{iLkWkmShifts}} δ i = cong vr (shiftIx-wkm δ i)

--------------------------------------------------------------------------------
