
module UniDB.Subst.Core where

open import UniDB.Spec public
open import UniDB.Morph.Unit

record Ap (T X : STX) : Set₁ where
  field
    ap : {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
      {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (x : X γ₁) → X γ₂
open Ap {{...}} public

record ApVr (T : STX) {{vrT : Vr T}} {{apTT : Ap T T}} : Set₁ where
  field
    ap-vr :
      {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
      {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) →
      (i : Ix γ₁) → ap {T} ξ (vr i) ≡ lk {T} ξ i
open ApVr {{...}} public

record LkCompAp
  (T : STX) {{vrT : Vr T}} {{apTT : Ap T T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{compΞ : Comp Ξ}} : Set₁ where
  field
    lk-⊙-ap : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃)
      (i : Ix γ₁) → lk {T} (ξ₁ ⊙ ξ₂) i ≡ ap {T} ξ₂ (lk ξ₁ i)
open LkCompAp {{...}} public

record ApIdm
  (T : STX) {{vrT : Vr T}}
  (X : STX) {{apTX : Ap T X}} : Set₁ where
  field
    ap-idm :
      {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{idmΞ : Idm Ξ}}
      {{lkIdmTΞ : LkIdm T Ξ}} {{upIdmΞ : UpIdm Ξ}}
      {γ : Dom} (x : X γ) →
      ap {T} (idm {Ξ} γ) x ≡ x
open ApIdm {{...}} public

record ApRel
  (T : STX) {{vrT : Vr T}}
  (X : STX) {{apTX : Ap T X}} : Set₁ where
  field
    ap-rel≅ :
      {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
      {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}}
      {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} (hyp : [ T ] ξ ≅ ζ)
      (x : X γ₁) → ap {T} ξ x ≡ ap {T} ζ x

  ap-rel≃ :  {{wkT : Wk T}}
    {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
    {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}}
    {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} (hyp : [ T ] ξ ≃ ζ)
    (x : X γ₁) → ap {T} ξ x ≡ ap {T} ζ x
  ap-rel≃ hyp = ap-rel≅ (≃-to-≅` (≃-↑ hyp))
open ApRel {{...}} public

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  where

  record ApWkmWk : Set₁ where
    field
      ap-wkm-wk₁ :
        {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{wkmΞ : Wkm Ξ}}
        {{lkUpTΞ : LkUp T Ξ}} {{lkWkmTΞ : LkWkm T Ξ}}
        {γ : Dom} (x : X γ) →
        ap {T} (wkm {Ξ} 1) x ≡ wk₁ x
      ap-wkm-wk :
        {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{wkmΞ : Wkm Ξ}}
        {{lkUpTΞ : LkUp T Ξ}} {{lkWkmTΞ : LkWkm T Ξ}}
        {γ : Dom} (δ : Dom) (x : X γ) →
        ap {T} (wkm {Ξ} δ) x ≡ wk δ x

  open ApWkmWk {{...}} public

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}}
  where

  record ApWk : Set₁ where
    field
      ap-wk₁ :
        {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
        {{lkUpTΞ : LkUp T Ξ}}
        {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (x : X γ₁) →
        ap {T} (ξ ↑₁) (wk₁ x) ≡ wk₁ (ap {T} ξ x)
  open ApWk {{...}} public

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  (X : STX) {{apTX : Ap T X}}
  where

  record ApComp : Set₁ where
    field
      ap-⊙ :
        {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{compΞ : Comp Ξ}}
        {{upCompΞ : UpComp Ξ}} {{lkCompTΞ : LkCompAp T Ξ}}
        {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) →
          (x : X γ₁) → ap {T} (ξ₁ ⊙ ξ₂) x ≡ ap {T} ξ₂ (ap {T} ξ₁ x)
  open ApComp {{...}} public

instance
  iApIx : Ap Ix Ix
  ap {{iApIx}} = lk

  iApVrIx : ApVr Ix
  ap-vr {{iApVrIx}} ξ i = refl

  iApIdmIxIx : ApIdm Ix Ix
  ap-idm {{iApIdmIxIx}} {Ξ} = lk-idm {Ix} {Ξ}

  iApWkmWkIxIx : ApWkmWk Ix Ix
  ap-wkm-wk₁ {{iApWkmWkIxIx}} {Ξ} = lk-wkm {Ix} {Ξ} 1
  ap-wkm-wk {{iApWkmWkIxIx}} {Ξ} = lk-wkm {Ix} {Ξ}

  iApRelIxIx : ApRel Ix Ix
  ap-rel≅ {{iApRelIxIx}} = lk≃ ∘ ≅-to-≃

  iApWkIxIx : ApWk Ix Ix
  ap-wk₁ {{iApWkIxIx}} {Ξ} ξ i = lk-↑₁-suc {Ix} {Ξ} ξ i

-- TODO: Remove
module _
  (T : STX) {{vrT : Vr T}} {{apTT : Ap T T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
  (Ζ : MOR) {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}}
  (Θ : MOR) {{lkTΘ : Lk T Θ}} {{upΘ : Up Θ}}
  {{hcompΞΖΘ : HComp Ξ Ζ Θ}}
  where

  record LkHCompAp : Set₁ where
    field
      lk-⊡-ap : {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃)
        (i : Ix γ₁) → lk {T} {Θ} (ξ ⊡ ζ) i ≡ ap {T} ζ (lk ξ i)
  open LkHCompAp {{...}} public

-- TODO: Remove
module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  (X : STX) {{apTX : Ap T X}}
  where

  record ApHComp : Set₁ where
    field
      ap-⊡ :
        {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
        {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}}
        {Θ : MOR} {{lkTΘ : Lk T Θ}} {{upΘ : Up Θ}}
        {{hcompΞΖΘ : HComp Ξ Ζ Θ}} {{upHCompΞ : UpHComp Ξ Ζ Θ}}
        {{lkHCompTΞΖΘ : LkHCompAp T Ξ Ζ Θ}}
        {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) →
          (x : X γ₁) → ap {T} {X} {Θ} (ξ ⊡ ζ) x ≡ ap {T} ζ (ap {T} ξ x)
  open ApHComp {{...}} public

-- TODO: Move
module _
  {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{wkVrT : WkVr T}}
  {X : STX} {{wkX : Wk X}} {{apTX : Ap T X}} {{apRelTX : ApRel T X}} {{apIdmTX : ApIdm T X}}
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{idmΞ : Idm Ξ}} {{lkIdmTΞ : LkIdm T Ξ}}
  {{lkUpTΞ : LkUp T Ξ}}
  where

  ap-idm` : {γ : Dom} (x : X γ) → ap {T} (idm {Ξ} γ) x ≡ x
  ap-idm` {γ} x = begin
    ap {T} (idm {Ξ} γ) x    ≡⟨ ap-rel≃ {T} lem x ⟩
    ap {T} (idm {Unit} γ) x ≡⟨ ap-idm {T} x ⟩
    x ∎
    where
      lem : [ T ] idm {Ξ} γ ≃ unit
      lk≃ lem = lk-idm {T} {Ξ}
