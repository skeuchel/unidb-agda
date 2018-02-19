
module UniDB.Morph.Unit where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Unit : MOR where
  unit : {γ : Dom} → Unit γ γ

instance
  iUpUnit : Up Unit
  _↑₁ {{iUpUnit}} unit = unit
  _↑_ {{iUpUnit}} unit δ = unit
  ↑-zero {{iUpUnit}} unit = refl
  ↑-suc {{iUpUnit}} unit δ = refl

  iIdmUnit : Idm Unit
  idm {{iIdmUnit}} _ = unit

  iCompUnit : Comp Unit
  _⊙_ {{iCompUnit}} unit unit = unit

  iUpIdmUnit : UpIdm Unit
  idm-↑₁ {{iUpIdmUnit}} = refl

module _ {T : STX} {{vrT : Vr T}} where

  instance
    iLkUnit :  Lk T Unit
    lk {{iLkUnit}} unit = vr {T = T}

    iLkUpUnit : {{wkT : Wk T}} {{wkVrT : WkVr T}} → LkUp T Unit
    lk-↑₁-zero {{iLkUpUnit}} unit  = refl
    lk-↑₁-suc {{iLkUpUnit}} unit i = sym (wk₁-vr {T = T} i)

    iLkIdmUnit : LkIdm T Unit
    lk-idm {{iLkIdmUnit}} i = refl

--------------------------------------------------------------------------------
