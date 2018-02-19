
module UniDB.Morph.WeakenPrime where

open import UniDB.Spec
open import UniDB.Morph.ShiftsPrime
open import Function

--------------------------------------------------------------------------------

data Weaken` : MOR where
  baseW : {γ : Dom} → Weaken` γ γ
  stepW : {γ₁ γ₂ : Dom} → Weaken` γ₁ γ₂  → Weaken` γ₁ (suc γ₂)

lkWeakenIx` : {γ₁ γ₂ : Dom} → Weaken` γ₁ γ₂ → Ix γ₁ → Ix γ₂
lkWeakenIx` baseW     i = i
lkWeakenIx` (stepW ξ) i = suc (lkWeakenIx` ξ i)

instance
  iLkWeaken` : {T : STX} {{vrT : Vr T}} → Lk T Weaken`
  lk {{iLkWeaken`}} ξ i = vr (lkWeakenIx` ξ i)

  iWkmWeaken` : Wkm Weaken`
  Wkm.wkm iWkmWeaken` zero    = baseW
  Wkm.wkm iWkmWeaken` (suc δ) = stepW (wkm {Weaken`} δ)

  iIdmWeaken` : Idm Weaken`
  idm {{iIdmWeaken`}} γ = baseW

  iWkWeaken` : {γ₁ : Dom} → Wk (Weaken` γ₁)
  wk₁ {{iWkWeaken`}} ξ = stepW ξ
  wk {{iWkWeaken`}} zero x = x
  wk {{iWkWeaken`}} (suc δ) x = wk₁ (wk δ x)
  wk-zero {{iWkWeaken`}} x = refl
  wk-suc {{iWkWeaken`}} δ x = refl

lkWeakenIx`-wkm : {γ : Dom} (δ : Dom) (i : Ix γ) →
  lkWeakenIx` (wkm {Weaken`} δ) i ≡ wk δ i
lkWeakenIx`-wkm zero    i = refl
lkWeakenIx`-wkm (suc δ) i = cong suc (lkWeakenIx`-wkm δ i)

instance
  iLkWkmWeaken` : {T : STX} {{vrT : Vr T}} → LkWkm T Weaken`
  lk-wkm {{iLkWkmWeaken` {T}}} δ i = cong (vr {T}) (lkWeakenIx`-wkm δ i)

  iCompWeaken` : Comp Weaken`
  _⊙_ {{iCompWeaken`}} ξ baseW      = ξ
  _⊙_ {{iCompWeaken`}} ξ (stepW ξ₂) = stepW (ξ ⊙ ξ₂)

wk-comp` : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken` γ₁ γ₂) (ξ₂ : Weaken` γ₂ γ₃)
  (δ : Dom) → wk δ (ξ₁ ⊙ ξ₂) ≡ ξ₁ ⊙ wk δ ξ₂
wk-comp` ξ₁ ξ₂ zero    = refl
wk-comp` ξ₁ ξ₂ (suc δ) = cong stepW (wk-comp` ξ₁ ξ₂ δ)

lkIx-wk-weaken` : {γ₁ γ₂ : Dom} (δ : Dom) (ξ : Weaken` γ₁ γ₂) (i : Ix γ₁) →
  lk {Ix} {Weaken`} (wk δ ξ) i ≡ wk δ (lk {Ix} {Weaken`} ξ i)
lkIx-wk-weaken` zero    ξ i = refl
lkIx-wk-weaken` (suc δ) ξ i = cong suc (lkIx-wk-weaken` δ ξ i)

module _ (T : STX) {{vrT : Vr T}}  {{wkT : Wk T}} {{wkVrT : WkVr T}} where

  lk-wk₁-weaken` :
    {γ₁ γ₂ : Dom} (ξ : Weaken` γ₁ γ₂) (i : Ix γ₁) →
    lk {T} {Weaken`} (wk₁ ξ) i ≡ wk₁ (lk {T} {Weaken`} ξ i)
  lk-wk₁-weaken` ξ i = sym (wk₁-vr {T} (lk {Ix} {Weaken`} ξ i) )

  lk-wk-weaken` :
    {γ₁ γ₂ : Dom} (δ : Dom) (ξ : Weaken` γ₁ γ₂) (i : Ix γ₁) →
    lk {T} {Weaken`} (wk δ ξ) i ≡ wk δ (lk {T} {Weaken`} ξ i)
  lk-wk-weaken` δ ξ i = trans
    (cong (vr {T}) (lkIx-wk-weaken` δ ξ i))
    (sym (wk-vr {T} δ (lk {Ix} {Weaken`} ξ i)))

lkWeakenIx`-comp :
  {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken` γ₁ γ₂) (ξ₂ : Weaken` γ₂ γ₃)
  (i : Ix γ₁) →
  lkWeakenIx` ((iCompWeaken` Comp.⊙ ξ₁) ξ₂) i ≡
  lkWeakenIx` ξ₂ (lkWeakenIx` ξ₁ i)
lkWeakenIx`-comp ξ₁ baseW      i = refl
lkWeakenIx`-comp ξ₁ (stepW ξ₂) i = cong suc (lkWeakenIx`-comp ξ₁ ξ₂ i)

instance
  iLkRenWeaken` : {T : STX} {{vrT : Vr T}} → LkRen T Weaken`
  lk-ren {{iLkRenWeaken`}} ξ i = refl

  iLkRenCompWeaken` : {T : STX} {{vrT : Vr T}} → LkRenComp T Weaken`
  lk-ren-comp {{iLkRenCompWeaken` {T}}} ξ₁ ξ₂ i =
    cong (vr {T}) (lkWeakenIx`-comp ξ₁ ξ₂ i)

  iCompIdmWeaken` : CompIdm Weaken`
  ⊙-idm {{iCompIdmWeaken`}} ξ = refl
  idm-⊙ {{iCompIdmWeaken`}} baseW = refl
  idm-⊙ {{iCompIdmWeaken`}} (stepW ξ) = cong stepW (idm-⊙ {Weaken`} ξ)

  iCompAssocWeaken` : CompAssoc Weaken`
  ⊙-assoc {{iCompAssocWeaken`}} ξ₁ ξ₂ baseW      = refl
  ⊙-assoc {{iCompAssocWeaken`}} ξ₁ ξ₂ (stepW ξ₃) =
    cong stepW (⊙-assoc {Weaken`} ξ₁ ξ₂ ξ₃)

⊙-wkm-weaken` : {γ₁ γ₂ : Dom} (ξ : Weaken` γ₁ γ₂) (δ : Dom) →
  ξ ⊙ wkm {Weaken`} δ ≡ wk δ ξ
⊙-wkm-weaken` ξ zero = refl
⊙-wkm-weaken` ξ (suc δ) = cong stepW (⊙-wkm-weaken` ξ δ)

extensionality-weaken` : {γ₁ γ₂ : Dom} (ξ₁ ξ₂ : Weaken` γ₁ γ₂)
  (hyp : (i : Ix γ₁) → lk {Ix} ξ₁ i ≡ lk {Ix} ξ₂ i) →
  ξ₁ ≡ ξ₂
extensionality-weaken` baseW baseW           hyp = refl
extensionality-weaken` baseW (stepW ξ₂)      hyp = case hyp zero of λ ()
extensionality-weaken` (stepW ξ₁) baseW      hyp = case hyp zero of λ ()
extensionality-weaken` (stepW ξ₁) (stepW ξ₂) hyp =
  cong stepW (extensionality-weaken` ξ₁ ξ₂ (suc-inj ∘ hyp))

--------------------------------------------------------------------------------
