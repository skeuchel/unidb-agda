
module UniDB.Morph.Shift where

open import UniDB.Spec
open import UniDB.Morph.Depth
open import UniDB.Morph.Weaken

--------------------------------------------------------------------------------

data Shift : MOR where
  shift : {γ₁ γ₂ : Dom} (ξ : Depth Weaken γ₁ γ₂) → Shift γ₁ γ₂

instance
  iUpShift : Up Shift
  _↑₁ {{iUpShift}} (shift ζ) = shift (ζ ↑₁)
  _↑_ {{iUpShift}} ξ 0 = ξ
  _↑_ {{iUpShift}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpShift}} ξ = refl
  ↑-suc {{iUpShift}} ξ δ⁺ = refl

  iWkmShift : Wkm Shift
  wkm {{iWkmShift}} δ = shift (depth (weaken δ) 0)

  iIdmShift : Idm Shift
  idm {{iIdmShift}} _ = wkm {Shift} 0

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkShift : Lk T Shift
    lk {{iLkShift}} (shift ζ) i = vr {T} (lk {Ix} {Depth Weaken} ζ i)

    iLkUpShift : {{wkT : Wk T}} {{wkVrT : WkVr T}} → LkUp T Shift
    lk-↑₁-zero {{iLkUpShift}} (shift ξ) = cong (vr {T}) (lk-↑₁-zero {Ix} {_} ξ )
    lk-↑₁-suc {{iLkUpShift}} (shift ξ) i = begin
      vr {T} (lk {Ix} (ξ ↑₁) (suc i)) ≡⟨ cong (vr {T}) (lk-↑₁-suc ξ i) ⟩
      vr {T} (wk₁ {Ix} (lk {Ix} ξ i)) ≡⟨ sym (wk₁-vr {T} (lk {Ix} ξ i)) ⟩
      wk₁ {T} (vr {T} (lk {Ix} ξ i))  ∎

    iLkWkmShift : LkWkm T Shift
    lk-wkm {{iLkWkmShift}} δ i = refl

    iLkIdmShift : LkIdm T Shift
    lk-idm {{iLkIdmShift}} i = refl

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkRenShift : LkRen T Shift
    lk-ren {{iLkRenShift}} (shift ξ) i = refl

--------------------------------------------------------------------------------
