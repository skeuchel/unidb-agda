
module UniDB.Morph.Reg where

open import UniDB.Spec
open import UniDB.Morph.WeakenPrime
open import UniDB.Morph.ShiftsPrime

--------------------------------------------------------------------------------

data Reg (T : STX) : MOR where
  baseR : {γ₁ γ₂ : Dom} (ξ : Weaken` γ₁ γ₂) → Reg T γ₁ γ₂
  snocR : {γ₁ γ₂ : Dom} (ξ : Reg T γ₁ γ₂) (t : T γ₂) → Reg T (suc γ₁) γ₂

module _ {T : STX} where

  instance
    iIdmReg : Idm (Reg T)
    idm {{iIdmReg}} γ = baseR baseW

    iWkmReg : Wkm (Reg T)
    wkm {{iWkmReg}} δ = baseR (wkm {Weaken`} δ)

    iBetaReg : Beta T (Reg T)
    beta {{iBetaReg}} t = snocR (idm {_} _) t

  module _ {{vrT : Vr T}} {{wkT : Wk T}} where

    instance
      iWkReg : {γ₁ : Dom} → Wk (Reg T γ₁)
      wk₁ {{iWkReg}} (baseR ξ)    = baseR (wk₁ ξ)
      wk₁ {{iWkReg}} (snocR ξ t) = snocR (wk₁ ξ) (wk₁ t)
      wk {{iWkReg}} zero ξ       = ξ
      wk {{iWkReg}} (suc δ) ξ    = wk₁ (wk δ ξ)
      wk-zero {{iWkReg}} x = refl
      wk-suc {{iWkReg}} δ x = refl

      iUpReg : Up (Reg T)
      _↑₁ {{iUpReg}} ξ = snocR (wk₁ ξ) (vr {T} zero)
      _↑_ {{iUpReg}} ξ 0 = ξ
      _↑_ {{iUpReg}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
      ↑-zero {{iUpReg}} ξ = refl
      ↑-suc {{iUpReg}} ξ δ⁺ = refl

      -- iUpIdmReg : {{wkT : Wk T}} → UpIdm (Reg T)
      -- idm-↑₁ {{iUpIdmReg}} = ?refl

  instance
    iHCompWeakenReg : HComp Weaken` (Reg T) (Reg T)
    _⊡_ {{iHCompWeakenReg}} ξ         (baseR ζ)   = baseR (ξ ⊙ ζ)
    _⊡_ {{iHCompWeakenReg}} baseW     ζ           = ζ
    _⊡_ {{iHCompWeakenReg}} (stepW ξ) (snocR ζ t) = ξ ⊡ ζ

    iHCompIdmLeftWeakenReg : HCompIdmLeft Weaken` (Reg T)
    idm-⊡ {{iHCompIdmLeftWeakenReg}} (baseR ξ)
      rewrite idm-⊙ {Weaken`} ξ = refl
    idm-⊡ {{iHCompIdmLeftWeakenReg}} (snocR ξ₂ t) = refl

  ⊡-⊡-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom}
    (ξ₁ : Weaken` γ₁ γ₂)
    (ξ₂ : Weaken` γ₂ γ₃)
    (ξ₃ : Reg T γ₃ γ₄) →
    _⊡_ {Weaken`} {Reg T} {Reg T} ξ₁ (ξ₂ ⊡ ξ₃) ≡ (ξ₁ ⊙ ξ₂) ⊡ ξ₃
  ⊡-⊡-assoc ξ₁ ξ₂ (baseR ξ₃) = cong baseR (⊙-assoc {Weaken`} ξ₁ ξ₂ ξ₃)
  ⊡-⊡-assoc ξ₁ baseW ξ₃ rewrite idm-⊡ {Weaken`} {Reg T} ξ₃ = refl
  ⊡-⊡-assoc ξ₁ (stepW ξ₂) (snocR ξ₃ t) = ⊡-⊡-assoc ξ₁ ξ₂ ξ₃

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkReg : Lk T (Reg T)
    lk {{iLkReg}} (baseR ξ)   i       = lk {T} {Weaken`} ξ i
    lk {{iLkReg}} (snocR ξ t) zero    = t
    lk {{iLkReg}} (snocR ξ t) (suc i) = lk {T} {Reg T} ξ i

    iLkIdmReg : LkIdm T (Reg T)
    lk-idm {{iLkIdmReg}} i = refl

    iLkWkmReg : {{wkT : Wk T}} → LkWkm T (Reg T)
    lk-wkm {{iLkWkmReg}} = lk-wkm {T} {Weaken`}

    iLkUpReg : {{wkT : Wk T}} {{wkVrT : WkVr T}} → LkUp T (Reg T)
    lk-↑₁-zero {{iLkUpReg}} ξ = refl
    lk-↑₁-suc {{iLkUpReg}} (baseR ξ)   i       = sym (wk₁-vr {T} (lk {Ix} {Weaken`} ξ i))
    lk-↑₁-suc {{iLkUpReg}} (snocR ξ t) zero    = refl
    lk-↑₁-suc {{iLkUpReg}} (snocR ξ t) (suc i) = lk-↑₁-suc {T} {Reg T} ξ i

--------------------------------------------------------------------------------
