
module UniDB.Basic where

open import UniDB.Spec
open import UniDB.Subst
open import Function

module _
  {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} {{apVrT : ApVr T}} {{apWkTT : ApWk T T}}
  {Ξ : MOR} {{upΞ : Up Ξ}} {{compΞ : Comp Ξ}} {{lkTΞ : Lk T Ξ}} {{lkUpTΞ : LkUp T Ξ}}
    {{lkCompTΞ : LkCompAp T Ξ}} where

  ⊙-↑₁-pointwise : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) →
    [ T ] ((ξ₁ ⊙ ξ₂) ↑₁) ≃ (ξ₁ ↑₁ ⊙ ξ₂ ↑₁)
  lk≃ (⊙-↑₁-pointwise ξ₁ ξ₂) zero = begin
    lk {T} ((ξ₁ ⊙ ξ₂) ↑₁) zero          ≡⟨ lk-↑₁-zero (ξ₁ ⊙ ξ₂) ⟩
    vr zero                             ≡⟨ sym (lk-↑₁-zero ξ₂) ⟩
    lk (ξ₂ ↑₁) zero                     ≡⟨ sym (ap-vr {T} (ξ₂ ↑₁) zero) ⟩
    ap {T} (ξ₂ ↑₁) (vr zero)            ≡⟨ cong (ap {T} (ξ₂ ↑₁)) (sym (lk-↑₁-zero ξ₁)) ⟩
    ap {T} (ξ₂ ↑₁) (lk (ξ₁ ↑₁) zero)    ≡⟨ sym (lk-⊙-ap {T} (ξ₁ ↑₁) (ξ₂ ↑₁) zero) ⟩
    lk (ξ₁ ↑₁ ⊙ ξ₂ ↑₁) zero             ∎
  lk≃ (⊙-↑₁-pointwise ξ₁ ξ₂) (suc i) = begin
    lk ((ξ₁ ⊙ ξ₂) ↑₁) (wk₁ i)           ≡⟨ lk-↑₁-suc (ξ₁ ⊙ ξ₂) i ⟩
    wk₁ (lk (ξ₁ ⊙ ξ₂) i)                ≡⟨ cong wk₁ (lk-⊙-ap {T} ξ₁ ξ₂ i) ⟩
    wk₁ (ap {T} ξ₂ (lk ξ₁ i))           ≡⟨ sym (ap-wk₁ {T} ξ₂ (lk ξ₁ i)) ⟩
    ap {T} (ξ₂ ↑₁) (wk₁ (lk ξ₁ i))      ≡⟨ cong (ap {T} (ξ₂ ↑₁)) (sym (lk-↑₁-suc ξ₁ i)) ⟩
    ap {T} (ξ₂ ↑₁) (lk (ξ₁ ↑₁) (wk₁ i)) ≡⟨ sym (lk-⊙-ap {T} (ξ₁ ↑₁) (ξ₂ ↑₁) (wk₁ i) ) ⟩
    lk (ξ₁ ↑₁ ⊙ ξ₂ ↑₁) (wk₁ i)          ∎
