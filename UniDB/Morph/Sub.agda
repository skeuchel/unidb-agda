
module UniDB.Morph.Sub where

open import UniDB.Spec
open import UniDB.Morph.Depth

--------------------------------------------------------------------------------

data Single (T : STX) : MOR where
  single : {γ : Dom} (t : T γ) → Single T (suc γ) γ

instance
  iLkSingle : {T : STX} {{vrT : Vr T}} → Lk T (Single T)
  lk {{iLkSingle {T}}} (single t) zero    = t
  lk {{iLkSingle {T}}} (single t) (suc i) = vr {T} i

  iBetaSingle : {T : STX} → Beta T (Single T)
  beta {{iBetaSingle}} = single

--------------------------------------------------------------------------------

data Sub (T : STX) : MOR where
  sub : {γ₁ γ₂ : Dom} (ξ : Depth (Single T) γ₁ γ₂) → Sub T γ₁ γ₂

module _ {T : STX} where
  instance
    iLkSub : {{vrT : Vr T}} {{wkT : Wk T}} → Lk T (Sub T)
    lk {{iLkSub}} (sub ξ) = lk {T} {Depth (Single T)} ξ

    iUpSub : Up (Sub T)
    _↑₁ {{iUpSub}} (sub ζ)    = sub (ζ ↑₁)
    _↑_ {{iUpSub}} ξ 0        = ξ
    _↑_ {{iUpSub}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
    ↑-zero {{iUpSub}} ξ       = refl
    ↑-suc {{iUpSub}}  ξ δ     = refl

    iBetaSub : Beta T (Sub T)
    beta {{iBetaSub}} t = sub (beta {T} {Depth (Single T)} t)

--------------------------------------------------------------------------------
