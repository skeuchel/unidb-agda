
module UniDB.Subst.Pair where

open import UniDB.Subst.Core
open import UniDB.Morph.Pair

instance
  iLkPair :
    {T : STX} {{apTT : Ap T T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} →
    Lk T (Pair Ξ Ζ)
  lk {{iLkPair {T}}} (ξ ⊗ ζ) i = ap {T} ζ (lk {T} ξ i)

  iLkRenPair :
    {T : STX} {{vrT : Vr T}} {{apTT : Ap T T}} {{apVrT : ApVr T}}
    {Ξ : MOR} {{lkIxΞ : Lk Ix Ξ}} {{lkTΞ : Lk T Ξ}} {{lkRenTΞ : LkRen T Ξ}}
    {Ζ : MOR} {{lkIxΖ : Lk Ix Ζ}} {{lkTΖ : Lk T Ζ}} {{lkRenTΖ : LkRen T Ζ}} {{upΖ : Up Ζ}} →
    LkRen T (Pair Ξ Ζ)
  lk-ren {{iLkRenPair {T} {Ξ} {Ζ}}} (ξ ⊗ ζ) i = begin
    ap {T} ζ (lk {T} ξ i)        ≡⟨ cong (ap {T} ζ) (lk-ren {T} ξ i) ⟩
    ap {T} ζ (vr (lk {Ix} ξ i))  ≡⟨ ap-vr {T} ζ (lk {Ix} ξ i) ⟩
    lk {T} ζ (lk {Ix} ξ i)       ≡⟨ lk-ren {T} ζ (lk {Ix} ξ i) ⟩
    vr (lk {Ix} ζ (lk {Ix} ξ i)) ∎

  iLkHCompPair :
    {T : STX} {{vrT : Vr T}} {{apTT : Ap T T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} →
    LkHCompAp T Ξ Ζ (Pair Ξ Ζ)
  lk-⊡-ap {{iLkHCompPair}} ξ ζ i = refl

iLkUpPairRenaming :
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} {{apVrT : ApVr T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
  {{lkIxΞ : Lk Ix Ξ}} {{lkRenTΞ : LkRen T Ξ}} {{lkUpIxΞ : LkUp Ix Ξ}}
  (Ζ : MOR) {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}} →
  LkUp T (Pair Ξ Ζ)
lk-↑₁-zero {{iLkUpPairRenaming T Ξ Ζ}} (ξ ⊗ ζ) = begin
  ap {T} (ζ ↑₁) (lk {T} (ξ ↑₁) zero)     ≡⟨ cong (ap {T} (ζ ↑₁)) (lk-↑₁-zero ξ) ⟩
  ap {T} (ζ ↑₁) (vr zero)                ≡⟨ ap-vr {T} (ζ ↑₁) zero ⟩
  lk (ζ ↑₁) zero                         ≡⟨ lk-↑₁-zero ζ ⟩
  vr zero                                ∎
lk-↑₁-suc {{iLkUpPairRenaming T Ξ Ζ}} (ξ ⊗ ζ) i = begin
  ap {T} (ζ ↑₁) (lk (ξ ↑₁) (suc i))      ≡⟨ cong (ap {T} (ζ ↑₁)) (lk-ren (ξ ↑₁) (suc i)) ⟩
  ap {T} (ζ ↑₁) (vr (lk (ξ ↑₁) (suc i))) ≡⟨ ap-vr {T} (ζ ↑₁) (lk (ξ ↑₁) (suc i)) ⟩
  lk (ζ ↑₁) (lk (ξ ↑₁) (suc i))          ≡⟨ cong (lk (_↑₁ ζ)) (lk-↑₁-suc ξ i) ⟩
  lk (ζ ↑₁) (suc (lk ξ i))               ≡⟨ lk-↑₁-suc ζ (lk ξ i) ⟩
  wk₁ (lk ζ (lk ξ i))                    ≡⟨ cong wk₁ (sym (ap-vr {T} ζ (lk ξ i))) ⟩
  wk₁ (ap {T} ζ (vr (lk ξ i)))           ≡⟨ cong wk₁ (cong (ap {T} ζ) (sym (lk-ren ξ i))) ⟩
  wk₁ (ap {T} ζ (lk ξ i))                ∎

iLkUpPairSubstitution :
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} {{apVrT : ApVr T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
  (Ζ : MOR) {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}}
  (ap-wk₁-TΖ : {γ₁ γ₂ : Dom} (ζ : Ζ γ₁ γ₂) (t : T γ₁) →
    ap {T} (ζ ↑₁) (wk₁ t) ≡ wk₁ (ap {T} ζ t)) →
  LkUp T (Pair Ξ Ζ)
lk-↑₁-zero {{iLkUpPairSubstitution T Ξ Ζ ap-wk₁-TΖ}} (ξ ⊗ ζ) = begin
  ap {T} (ζ ↑₁) (lk (ξ ↑₁) zero) ≡⟨ cong (ap {T} (ζ ↑₁)) (lk-↑₁-zero ξ) ⟩
  ap {T} (ζ ↑₁) (vr zero)        ≡⟨ ap-vr {T} (ζ ↑₁) zero ⟩
  lk (ζ ↑₁) zero                 ≡⟨ lk-↑₁-zero  ζ ⟩
  vr zero                        ∎
lk-↑₁-suc {{iLkUpPairSubstitution T Ξ Ζ ap-wk₁-TΖ}} (ξ ⊗ ζ) i = begin
  ap {T} (ζ ↑₁) (lk (ξ ↑₁) (suc i)) ≡⟨ cong (ap {T} (ζ ↑₁)) (lk-↑₁-suc ξ i) ⟩
  ap {T} (ζ ↑₁) (wk₁ (lk ξ i))      ≡⟨ ap-wk₁-TΖ ζ (lk ξ i) ⟩
  wk₁ (ap {T} ζ (lk ξ i))           ∎

instance
  iLkUpPair :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
    {{apVrT : ApVr T}} {{apWkTT : ApWk T T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}} →
    LkUp T (Pair Ξ Ζ)
  iLkUpPair {T} {Ξ} {Ζ} = iLkUpPairSubstitution T Ξ Ζ (ap-wk₁ {T})

record ApPair (T : STX) {{apTT : Ap T T}} (X : STX) {{apTX : Ap T X}} : Set₁ where
  field
    ap-pair :
      {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
      {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}}
      {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃)
      (x : X γ₁) →
        ap {T} (ξ ⊗ ζ) x ≡ ap {T} ζ (ap {T} ξ x)
open ApPair {{...}} public

instance
  iApPairIxIx : ApPair Ix Ix
  ap-pair {{iApPairIxIx}} {Ξ} ξ ζ i = refl
