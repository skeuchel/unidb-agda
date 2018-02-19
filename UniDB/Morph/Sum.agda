
module UniDB.Morph.Sum where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Sum (Ξ Ζ : MOR) (γ₁ γ₂ : Dom) : Set where
  inl : Ξ γ₁ γ₂ → Sum Ξ Ζ γ₁ γ₂
  inr : Ζ γ₁ γ₂ → Sum Ξ Ζ γ₁ γ₂

instance
  iUpSum : {Ξ Ζ : MOR} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}} → Up (Sum Ξ Ζ)
  _↑₁ {{iUpSum}} (inl ξ) = inl (ξ ↑₁)
  _↑₁ {{iUpSum}} (inr ζ) = inr (ζ ↑₁)
  _↑_ {{iUpSum}} ξ 0 = ξ
  _↑_ {{iUpSum}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpSum}} ξ = refl
  ↑-suc {{iUpSum}} ξ δ⁺ = refl

  iLkSum :
    {T : STX}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} →
    Lk T (Sum Ξ Ζ)
  lk {{iLkSum {T} {Ξ} {Ζ}}} (inl ξ) i = lk {T} {Ξ} ξ i
  lk {{iLkSum {T} {Ξ} {Ζ}}} (inr ζ) i = lk {T} {Ζ} ζ i

  iLkUpSum :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}} →
    LkUp T (Sum Ξ Ζ)
  lk-↑₁-zero {{iLkUpSum {T} {Ξ} {Ζ}}} (inl ξ) = lk-↑₁-zero {T} {Ξ} ξ
  lk-↑₁-zero {{iLkUpSum {T} {Ξ} {Ζ}}} (inr ζ) = lk-↑₁-zero {T} {Ζ} ζ
  lk-↑₁-suc {{iLkUpSum {T} {Ξ} {Ζ}}} (inl ξ) = lk-↑₁-suc {T} {Ξ} ξ
  lk-↑₁-suc {{iLkUpSum {T} {Ξ} {Ζ}}} (inr ζ) = lk-↑₁-suc {T} {Ζ} ζ

module _
  (Ξ Ζ : MOR) {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  where

  inl-↑ : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (δ : Dom) →
    inl {Ξ} {Ζ} ξ ↑ δ ≡ inl (ξ ↑ δ)
  inl-↑ ξ zero    rewrite ↑-zero ξ              = refl
  inl-↑ ξ (suc δ) rewrite inl-↑ ξ δ | ↑-suc ξ δ = refl

  inr-↑ : {γ₁ γ₂ : Dom} (ζ : Ζ γ₁ γ₂) (δ : Dom) →
    inr {Ξ} {Ζ} ζ ↑ δ ≡ inr (ζ ↑ δ)
  inr-↑ ζ zero    rewrite ↑-zero ζ              = refl
  inr-↑ ζ (suc δ) rewrite inr-↑ ζ δ | ↑-suc ζ δ = refl

--------------------------------------------------------------------------------
