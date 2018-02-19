module UniDB.Subst.Inst where

open import UniDB.Spec
open import UniDB.Subst.Core
open import UniDB.Subst.Pair
open import UniDB.Subst.Shifts
open import UniDB.Morph.Pair
open import UniDB.Morph.Shift
open import UniDB.Morph.Shifts
open import UniDB.Morph.Unit

-- These are two unused instances. Just to show that ApHComp is slightly
-- stronger than ApPair, but given ApRel then ApPair and ApHComp become
-- equivalent.  Unfortunately neither ApPair nor ApHComp imply ApRel but
-- both can be made stronger to do so.
module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  (X : STX) {{apTX : Ap T X}} {{apHCompTX : ApHComp T X}}
  where

  iApPair : ApPair T X
  ap-pair {{iApPair}} {Ξ} {Ζ} ξ ζ x = ap-⊡ {T} {X} {Ξ} {Ζ} {Pair Ξ Ζ} ξ ζ x

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  {{apRelTX : ApRel T X}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{wkmΞ : Wkm Ξ}}
  {{lkUpTΞ : LkUp T Ξ}} {{lkWkmTΞ : LkWkm T Ξ}}
  (Ζ : MOR) {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{wkmΖ : Wkm Ζ}}
  {{lkUpTΖ : LkUp T Ζ}} {{lkWkmTΖ : LkWkm T Ζ}}
  where

  ap-wkm-rel : {γ : Dom} (δ : Dom) (x : X γ) →
    ap {T} (wkm {Ξ} δ) x ≡ ap {T} (wkm {Ζ} δ) x
  ap-wkm-rel {γ} δ = ap-rel≃ {T} lemma
    where
      lemma : [ T ] wkm {Ξ} {γ} δ ≃ wkm {Ζ} δ
      lk≃ lemma i = begin
        lk {T} (wkm {Ξ} δ) i ≡⟨ lk-wkm {T} {Ξ} δ i ⟩
        vr (wk δ i)          ≡⟨ sym (lk-wkm {T} {Ζ} δ i) ⟩
        lk {T} (wkm {Ζ} δ) i ∎

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  (X : STX) {{apTX : Ap T X}} {{apPairTX : ApPair T X}} {{apRelTX : ApRel T X}}
  where

  iApHComp : ApHComp T X
  ap-⊡ {{iApHComp}} {Ξ} {Ζ} {Θ} ξ ζ x = begin
    ap {T} {X} {Θ}        (ξ ⊡ ζ) x       ≡⟨ ap-rel≅ {T} (≃-to-≅` lem) x ⟩
    ap {T} {X} {Pair Ξ Ζ} (ξ ⊡ ζ) x       ≡⟨ ap-pair {T} ξ ζ x ⟩
    ap {T} {X} {Ζ} ζ (ap {T} {X} {Ξ} ξ x) ∎
    where
      lem : (δ : Dom) → [ T ] ((_⊡_ {Θ = Θ} ξ ζ) ↑ δ) ≃ (ξ ⊗ ζ) ↑ δ
      lk≃ (lem δ) i = begin
        lk {T} {Θ}          ((ξ ⊡ ζ) ↑ δ) i   ≡⟨ cong (λ ρ → lk {T} {Θ} ρ i) (⊡-↑ {Ξ} {Ζ} {Θ} ξ ζ δ) ⟩
        lk {T} {Θ}          (ξ ↑ δ ⊡ ζ ↑ δ) i ≡⟨ lk-⊡-ap {T} {Ξ} {Ζ} {Θ} (ξ ↑ δ) (ζ ↑ δ) i ⟩
        lk {T} {Pair Ξ Ζ} (ξ ↑ δ ⊗ ζ ↑ δ) i ≡⟨ cong (λ ρ → lk {T} {Pair Ξ Ζ} ρ i) (sym (⊡-↑ {Ξ} {Ζ} {Pair Ξ Ζ} ξ ζ δ)) ⟩
        lk {T} {Pair Ξ Ζ} ((ξ ⊗ ζ) ↑ δ) i   ∎

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  (X : STX) {{apTX : Ap T X}} {{apPairTX : ApPair T X}} {{apRelTX : ApRel T X}}
  where

  iApComp : ApComp T X
  ap-⊙ {{iApComp}} {Ξ} ξ ζ x = begin
    ap {T} (ξ ⊙ ζ) x      ≡⟨ ap-rel≅ {T} (≃-to-≅` lem) x ⟩
    ap {T} (ξ ⊗ ζ) x      ≡⟨ ap-pair {T} ξ ζ x ⟩
    ap {T} ζ (ap {T} ξ x)  ∎
    where
      lem : (δ : Dom) → [ T ] (ξ ⊙ ζ) ↑ δ ≃ (ξ ⊗ ζ) ↑ δ
      lk≃ (lem δ) i = begin
        lk ((ξ ⊙ ζ) ↑ δ) i           ≡⟨ cong (λ ρ → lk ρ i) (⊙-↑ ξ ζ δ) ⟩
        lk (ξ ↑ δ ⊙ ζ ↑ δ) i         ≡⟨ lk-⊙-ap (ξ ↑ δ) (ζ ↑ δ) i ⟩
        ap {T} (ζ ↑ δ) (lk (ξ ↑ δ) i) ≡⟨ refl ⟩
        lk (ξ ↑ δ ⊗ ζ ↑ δ) i         ≡⟨ refl ⟩ -- cong (λ ρ → lk ρ i) (sym (⊡-↑ {Ξ} {Ξ} {Pair Ξ Ξ} ξ ζ δ)) ⟩
        lk ((ξ ⊗ ζ) ↑ δ) i           ∎

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  {{apVrT : ApVr T}} {{apWkmWkTT : ApWkmWk T T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  {{apWkmWkTX : ApWkmWk T X}}
  {{apPairTX : ApPair T X}} {{apRelTX : ApRel T X}}
  (Ρ : MOR) {{lkTΡ : Lk T Ρ}} {{upΡ : Up Ρ}} {{lkUpTΡ : LkUp T Ρ}}
  {{wkmΡ : Wkm Ρ}} {{lkWkmΡ : LkWkm T Ρ}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
  {{lkUpPairΞΡ : LkUp T (Pair Ξ Ρ)}}
  {{lkUpPairΞΡ : LkUp T (Pair Ρ Ξ)}}
  where

  ap-wk₁-gen : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (x : X γ₁) →
    ap {T} {X} {Ξ} (ξ ↑₁) (wk₁ x) ≡ wk₁ (ap {T} {X} {Ξ} ξ x)
  ap-wk₁-gen ξ x = begin
    ap {T} (ξ ↑₁) (wk₁ x)                ≡⟨ cong (ap {T} (ξ ↑₁)) (sym (ap-wkm-wk₁ {T} {X} {Ρ} x)) ⟩
    ap {T} (ξ ↑₁) (ap {T} (wkm {Ρ} 1) x) ≡⟨ sym (ap-pair {T} (wkm {Ρ} 1) (ξ ↑₁) x) ⟩
    ap {T} (wkm {Ρ} 1 ⊗ ξ ↑₁) x         ≡⟨ ap-rel≃ {T} lem x ⟩
    ap {T} (ξ ⊗ wkm {Ρ} 1) x            ≡⟨ ap-pair {T} ξ (wkm {Ρ} 1) x ⟩
    ap {T} (wkm {Ρ} 1) (ap {T} ξ x)      ≡⟨ ap-wkm-wk₁ {T} (ap {T} ξ x) ⟩
    wk₁ (ap {T} ξ x)
    ∎
    where
      lem : [ T ] (wkm {Ρ} 1 ⊗ ξ ↑₁) ≃ (ξ ⊗ wkm {Ρ} 1)
      lk≃ lem i = begin
        ap {T} (ξ ↑₁) (lk {T} (wkm {Ρ} 1) i) ≡⟨ cong (ap {T} (_↑₁ ξ)) (lk-wkm {T} {Ρ} 1 i) ⟩
        ap {T} (ξ ↑₁) (vr (suc i))           ≡⟨ ap-vr {T} (ξ ↑₁) (suc i) ⟩
        lk {T} (ξ ↑₁) (suc i)                ≡⟨ lk-↑₁-suc {T} ξ i ⟩
        wk₁ (lk {T} ξ i)                     ≡⟨ sym (ap-wkm-wk₁ {T} (lk {T} ξ i)) ⟩
        ap {T} (wkm {Ρ} 1) (lk {T} ξ i)      ∎

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  {{wkVrT : WkVr T}}
  {{apVrT : ApVr T}} {{apWkmWkTT : ApWkmWk T T}}
  {{apPairTT : ApPair T T}} {{apRelTT : ApRel T T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  {{apWkmWkTX : ApWkmWk T X}}
  {{apPairTX : ApPair T X}} {{apRelTX : ApRel T X}}
  where

  private
    Ren : MOR
    Ren = Shift

  iApWk : ApWk T X
  ap-wk₁ {{iApWk}} {Ξ} = ap-wk₁-gen T X Ren Ξ
    where
      instance
        iLkUpRenRen : LkUp T (Pair Ren Ren)
        iLkUpRenRen = iLkUpPairRenaming T Ren Ren
        iLkUpRenΞ : LkUp T (Pair Ren Ξ)
        iLkUpRenΞ = iLkUpPairRenaming T Ren Ξ
        iLkUpΞRen : LkUp T (Pair Ξ Ren)
        iLkUpΞRen = iLkUpPairSubstitution T Ξ Ren
          (ap-wk₁-gen T T Ren Ren)

{-
module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  {{wkVrT : WkVr T}} {{apVrT : ApVr T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  {{apWkmWkTX : ApWkmWk T X}} {{apIdmTX : ApIdm T X}} {{apCompTX : ApComp T X}}
  where

  private
    module _
      (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
      {{idmΞ : Idm Ξ}} {{wkmΞ : Wkm Ξ}} {{compΞ : Comp Ξ}}
      {{lkUpTΞ : LkUp T Ξ}} {{lkWkmTΞ : LkWkm T Ξ}} {{lkIdmTΞ : LkIdm T Ξ}}
      {{upIdmΞ : UpIdm Ξ}} {{upCompΞ : UpComp Ξ}} {{lkCompTΞ : LkCompAp T Ξ}}
      {{wkmHomΞ : WkmHom Ξ}}
      where

      iWkHom` : WkHom X
      wk-zero {{iWkHom`}} x = begin
        wk 0 x                                    ≡⟨ sym (ap-wkm-wk T X Ξ 0 x) ⟩
        ap T X Ξ (wkm Ξ 0) x                      ≡⟨ cong (λ ξ → ap T X Ξ ξ x) (wkm-zero Ξ) ⟩
        ap T X Ξ (idm Ξ _) x                      ≡⟨ ap-idm T X Ξ x ⟩
        x ∎
      wk-suc  {{iWkHom`}} δ x = begin
        wk (suc δ) x                              ≡⟨ sym (ap-wkm-wk T X Ξ (suc δ) x) ⟩
        ap T X Ξ (wkm Ξ (suc δ)) x                ≡⟨ cong (λ ξ → ap T X Ξ ξ x) (wkm-suc Ξ δ) ⟩
        ap T X Ξ (wkm Ξ δ ⊙ wkm Ξ 1) x            ≡⟨ ap-⊙ T X Ξ (wkm Ξ δ) (wkm Ξ 1) x ⟩
        ap T X Ξ (wkm Ξ 1) (ap T X Ξ (wkm Ξ δ) x) ≡⟨ ap-wkm-wk₁ T X Ξ (ap T X Ξ (wkm Ξ δ) x) ⟩
        wk₁ (ap T X Ξ (wkm Ξ δ) x)                ≡⟨ cong wk₁ (ap-wkm-wk T X Ξ δ x) ⟩
        wk₁ (wk δ x)                              ∎

  iWkHom : WkHom X
  iWkHom = iWkHom` Shifts
-}
