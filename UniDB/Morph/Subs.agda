
module UniDB.Morph.Subs where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Subs (T : STX) : MOR where
  refl : {γ : Dom} → Subs T γ γ
  step : {γ₁ γ₂ : Dom} (ξ : Subs T γ₁ γ₂) (t : T γ₂) → Subs T (suc γ₁) γ₂
  skip : {γ₁ γ₂ : Dom} (ξ : Subs T γ₁ γ₂) → Subs T (suc γ₁) (suc γ₂)

instance
  iUpSubs : {T : STX} → Up (Subs T)
  _↑₁    {{iUpSubs}}            = skip
  _↑_    {{iUpSubs}} ξ 0        = ξ
  _↑_    {{iUpSubs}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpSubs}} ξ          = refl
  ↑-suc  {{iUpSubs}} ξ δ        = refl

module _ {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} where

  instance
    iLkSubs : Lk T (Subs T)
    lk {{iLkSubs}} refl       i       = vr {T} i
    lk {{iLkSubs}} (step ξ t) zero    = t
    lk {{iLkSubs}} (step ξ t) (suc i) = lk {T} {Subs T} ξ i
    lk {{iLkSubs}} (skip ξ)   zero    = vr {T} zero
    lk {{iLkSubs}} (skip ξ)   (suc i) = wk₁ (lk {T} {Subs T} ξ i)

--------------------------------------------------------------------------------
