
module UniDB.Morph.Weaken where

open import UniDB.Spec

--------------------------------------------------------------------------------

data Weaken : MOR where
  weaken : {γ : Dom} (δ : Dom) → Weaken γ (γ ∪ δ)

instance
  iLkWeaken : {T : STX} {{vrT : Vr T}} → Lk T Weaken
  lk {{iLkWeaken}} (weaken δ) i = vr (wk δ i)

  iWkmWeaken : Wkm Weaken
  wkm {{iWkmWeaken}} = weaken

  iIdmWeaken : Idm Weaken
  idm {{iIdmWeaken}} γ = weaken 0

  iWkWeaken : {γ₁ : Dom} → Wk (Weaken γ₁)
  wk₁ {{iWkWeaken}} (weaken δ) = weaken (suc δ)
  wk {{iWkWeaken}} zero x = x
  wk {{iWkWeaken}} (suc δ) x = wk₁ (wk δ x)
  wk-zero {{iWkWeaken}} x = refl
  wk-suc {{iWkWeaken}} δ x = refl

  iLkWkmWeaken : {T : STX} {{vrT : Vr T}} → LkWkm T Weaken
  lk-wkm {{iLkWkmWeaken}} δ i = refl

  iCompWeaken : Comp Weaken
  _⊙_ {{iCompWeaken}} ξ (weaken δ) = wk δ ξ

wk₁-comp : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken γ₁ γ₂) (ξ₂ : Weaken γ₂ γ₃) →
  wk₁ (ξ₁ ⊙ ξ₂) ≡ ξ₁ ⊙ wk₁ ξ₂
wk₁-comp ξ₁ (weaken δ) = refl

wk-comp : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken γ₁ γ₂) (ξ₂ : Weaken γ₂ γ₃)
  (δ : Dom) → wk δ (ξ₁ ⊙ ξ₂) ≡ ξ₁ ⊙ wk δ ξ₂
wk-comp ξ₁ ξ₂ zero    = refl
wk-comp ξ₁ ξ₂ (suc δ) =
  trans (cong wk₁ (wk-comp ξ₁ ξ₂ δ)) (wk₁-comp ξ₁ (wk δ ξ₂))

module _ (T : STX) {{vrT : Vr T}} where

  lk-wk₁-weaken : {{wkT : Wk T}} {{wkVrT : WkVr T}}
    {γ₁ γ₂ : Dom} (ξ : Weaken γ₁ γ₂) (i : Ix γ₁) →
    lk {T} {Weaken} (wk₁ ξ) i ≡ wk₁ (lk {T} {Weaken} ξ i)
  lk-wk₁-weaken (weaken δ) i = sym (wk₁-vr {T} (wk δ i))

  lk-wk-weaken : {{wkT : Wk T}} {{wkVrT : WkVr T}}
    {γ₁ γ₂ : Dom} (δ : Dom) (ξ : Weaken γ₁ γ₂) (i : Ix γ₁) →
    lk {T} {Weaken} (wk δ ξ) i ≡ wk δ (lk {T} {Weaken} ξ i)
  lk-wk-weaken zero    ξ i = sym (wk-zero (lk {T} {Weaken} ξ i))
  lk-wk-weaken (suc δ) ξ i =
    trans
      (lk-wk₁-weaken (wk δ ξ) i)
      (trans
         (cong wk₁ (lk-wk-weaken δ ξ i))
         (sym (wk-suc {T} δ (lk {T} {Weaken} ξ i)))
      )

instance
  iLkRenWeaken : {T : STX} {{vrT : Vr T}} → LkRen T Weaken
  lk-ren {{iLkRenWeaken}} (weaken δ) i = refl

  iLkRenCompWeaken :
    {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{wkVrT : WkVr T}}  →
    LkRenComp T Weaken
  lk-ren-comp {{iLkRenCompWeaken {T}}} ξ₁ (weaken δ) i = begin
    lk {T} {Weaken} (wk δ ξ₁) i         ≡⟨ lk-wk-weaken T δ ξ₁ i ⟩
    wk δ (lk {T} {Weaken} ξ₁ i)         ≡⟨ cong (wk δ) (lk-ren {T} {Weaken} ξ₁ i) ⟩
    wk δ (vr {T} (lk {Ix} {Weaken} ξ₁ i)) ≡⟨ wk-vr {T} δ (lk {Ix} {Weaken} ξ₁ i) ⟩
    vr {T} (wk δ (lk {Ix} {Weaken} ξ₁ i)) ∎

  iCompIdmWeaken : CompIdm Weaken
  ⊙-idm {{iCompIdmWeaken}} ξ                = refl
  idm-⊙ {{iCompIdmWeaken}} (weaken zero)    = refl
  idm-⊙ {{iCompIdmWeaken}} (weaken (suc δ)) =
    cong wk₁ (idm-⊙ {Weaken} (weaken δ))

  iCompAssocWeaken : CompAssoc Weaken
  ⊙-assoc {{iCompAssocWeaken}} ξ₁ ξ₂ (weaken δ) = sym (wk-comp ξ₁ ξ₂ δ)

--------------------------------------------------------------------------------
