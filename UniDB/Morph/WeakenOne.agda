
module UniDB.Morph.WeakenOne where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Weaken₁ : MOR where
  weaken₁ : {γ : Dom} → Weaken₁ γ (suc γ)

instance
  iLkWeaken₁ : {T : STX} {{vrT : Vr T}} → Lk T Weaken₁
  lk {{iLkWeaken₁ {T}}} weaken₁ i = vr {T} (suc i)

  iLkRenWeaken₁ : {T : STX} {{vrT : Vr T}} → LkRen T Weaken₁
  lk-ren {{iLkRenWeaken₁}} weaken₁ i = refl

--------------------------------------------------------------------------------
