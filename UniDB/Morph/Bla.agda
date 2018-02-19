
module UniDB.Morph.Bla where

open import UniDB.Spec
open import UniDB.Morph.WeakenOne
open import UniDB.Morph.Sub
open import UniDB.Morph.ShiftsPrime
open import UniDB.Morph.Subs

-- mutual
--   data BlaSubst (T : STX) : MOR where
--     blasubst : {γ₁ γ₂ : Dom} → BlaSubst T γ₁ γ₂

mutual
  data BlaWeak* (T : STX) : MOR where
    reflW : {γ : Dom}     → BlaWeak* T γ γ
    inclW : {γ₁ γ₂ : Dom} → BlaWeak+ T γ₁ γ₂ → BlaWeak* T γ₁ γ₂
    skipW : {γ₁ γ₂ : Dom} → Bla T γ₁ γ₂ → BlaWeak* T (suc γ₁) (suc γ₂)

  data BlaWeak+ (T : STX) : MOR where
    stepW : {γ₁ γ₂ γ₃ : Dom} → Weaken₁ γ₁ γ₂ → BlaWeak* T γ₂ γ₃ → BlaWeak T γ₁ γ₃

  data BlaSubs* (T : STX) : MOR where
    reflS : {γ : Dom}     → BlaSubs* T γ γ
    inclS : {γ₁ γ₂ : Dom} → BlaSubs+ T γ₁ γ₂ → BlaSubs* T γ₁ γ₂
    skipS : {γ₁ γ₂ : Dom} → Bla T γ₁ γ₂ → BlaSubs* T (suc γ₁) (suc γ₂)

  data BlaSubs+ (T : STX) : MOR where
    stepS : {γ₁ γ₂ γ₃ : Dom} → BlaSubs* T γ₁ γ₂ → Single T γ₂ γ₃ → BlaWeak T γ₁ γ₃

  data Bla (T : STX) : MOR where
    refl : {γ : Dom} → Shifts* γ γ
    incl : {γ₁ γ₂ : Dom} (ξ : Shifts+ γ₁ γ₂) → Shifts* γ₁ γ₂

  data Shifts+ : MOR where
    step : {γ₁ γ₂ : Dom} (ξ : Shifts* γ₁ γ₂) → Shifts+ γ₁ (suc γ₂)
    skip : {γ₁ γ₂ : Dom} (ξ : Shifts+ γ₁ γ₂) → Shifts+ (suc γ₁) (suc γ₂)
