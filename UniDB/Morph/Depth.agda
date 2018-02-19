
module UniDB.Morph.Depth where

open import UniDB.Spec
open import Data.Sum

--------------------------------------------------------------------------------

data Depth (Ξ : MOR) : MOR where
  depth : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (δ : Dom) →
    Depth Ξ (γ₁ ∪ δ) (γ₂ ∪ δ)

Fin-∪ : {γ₁ : Dom} (γ₂ δ : Dom) (i : Ix (γ₁ ∪ δ)) → Ix γ₁ ⊎ Ix (γ₂ ∪ δ)
Fin-∪ γ₂ zero    i       = inj₁ i
Fin-∪ γ₂ (suc δ) zero    = inj₂ zero
Fin-∪ γ₂ (suc δ) (suc i) = map id suc (Fin-∪ γ₂ δ i)

instance
  iLkDepth :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} →
    Lk T (Depth Ξ)
  lk {{iLkDepth {T} {Ξ}}} (depth {γ₁} {γ₂} ξ δ) i with Fin-∪ γ₂ δ i
  ... | inj₁ j = wk δ (lk {T} {Ξ} ξ j)
  ... | inj₂ j = vr {T = T} j

  iUpDepth : {Ξ : MOR} → Up (Depth Ξ)
  _↑₁ {{iUpDepth}} (depth ξ δ) = depth ξ (suc δ)
  _↑_ {{iUpDepth {Ξ}}} ξ 0 = ξ
  _↑_ {{iUpDepth {Ξ}}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
  ↑-zero {{iUpDepth}} ξ = refl
  ↑-suc {{iUpDepth {Ξ}}} ξ δ⁺ = refl

  iWkmDepth : {Ξ : MOR} {{wkmΞ : Wkm Ξ}} → Wkm (Depth Ξ)
  wkm {{iWkmDepth {Ξ}}} δ = depth (wkm {Ξ} δ) 0

  iLkWkmDepth :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{wkVrT : WkVr T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{wkmΞ : Wkm Ξ}} {{lkWkmΞ : LkWkm T Ξ}} →
    LkWkm T (Depth Ξ)
  lk-wkm {{iLkWkmDepth {T} {Ξ}}} δ i = begin
    wk 0 (lk {T} {Ξ} (wkm δ) i) ≡⟨ wk-zero (lk {T} {Ξ} (wkm δ) i) ⟩
    lk {T} {Ξ} (wkm δ) i        ≡⟨ lk-wkm {T} {Ξ} δ i ⟩
    vr (wk δ i)         ∎

  iBetaDepth : {T : STX} {Ξ : MOR} {{betaTΞ : Beta T Ξ}} → Beta T (Depth Ξ)
  beta {{iBetaDepth {T} {Ξ}}} t = depth (beta {T} {Ξ} t) 0

  iLkUpDepth :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{wkVrT : WkVr T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} →
    LkUp T (Depth Ξ)
  lk-↑₁-zero {{iLkUpDepth {T} {Ξ}}} (depth ξ δ) = refl
  lk-↑₁-suc {{iLkUpDepth {T} {Ξ}}} (depth {γ₁} {γ₂} ξ δ) i with Fin-∪ γ₂ δ i
  ... | inj₁ j = wk-suc {T} δ (lk {T} {Ξ} ξ j)
  ... | inj₂ j = sym (wk₁-vr {T} j)

--------------------------------------------------------------------------------
