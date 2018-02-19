
module UniDB.Subst.Reg where

open import UniDB.Spec
open import UniDB.Subst.Core
open import UniDB.Morph.Reg
open import UniDB.Morph.WeakenPrime

module _ {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} where

  instance
    iCompReg : Comp (Reg T)
    _⊙_ {{iCompReg}} (baseR ξ)             ζ = ξ ⊡ ζ
    _⊙_ {{iCompReg}} (snocR {γ₁} {γ₂} ξ t) ζ = snocR (ξ ⊙ ζ) (ap {T} ζ t)

    iWkmHomReg : WkmHom (Reg T)
    wkm-zero {{iWkmHomReg}} = refl
    wkm-suc  {{iWkmHomReg}} δ = refl

    iWkmBetaReg : WkmBeta T (Reg T)
    wkm-beta {{iWkmBetaReg}} t = refl

  reg-zero : (γ : Dom) → Reg T zero γ
  reg-zero zero    = baseR baseW
  reg-zero (suc γ) = reg-zero γ ⊙ wkm {Reg T} 1

  complete : (γ₁ γ₂ : Dom) (f : Ix γ₁ → T γ₂) → Reg T γ₁ γ₂
  complete zero     γ₂ f = reg-zero γ₂
  complete (suc γ₁) γ₂ f = snocR (complete γ₁ γ₂ (f ∘ suc)) (f zero)

  ⊡-⊙-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom} (ξ₁ : Weaken` γ₁ γ₂) (ξ₂ : Reg T γ₂ γ₃) (ξ₃ : Reg T γ₃ γ₄) →
    ξ₁ ⊡ (ξ₂ ⊙ ξ₃) ≡ (ξ₁ ⊡ ξ₂) ⊙ ξ₃
  ⊡-⊙-assoc ξ₁        (baseR ξ₂)   ξ₃ = ⊡-⊡-assoc ξ₁ ξ₂ ξ₃
  ⊡-⊙-assoc baseW      ξ₂           ξ₃ rewrite idm-⊡ {Weaken`} {Reg T} (ξ₂ ⊙ ξ₃) | idm-⊡ {Weaken`} {Reg T} ξ₂ = refl
  ⊡-⊙-assoc (stepW ξ₁) (snocR ξ₂ t) ξ₃ = ⊡-⊙-assoc ξ₁ ξ₂ ξ₃

  wk₁-⊡ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken` γ₁ γ₂) (ξ₂ : Reg T γ₂ γ₃) →
    wk₁ (_⊡_ {Weaken`} {Reg T} {Reg T} ξ₁ ξ₂) ≡ ξ₁ ⊡ wk₁ ξ₂
  wk₁-⊡ ξ₁ (baseR ξ)            = refl
  wk₁-⊡ baseW (snocR ξ₂ t)      = refl
  wk₁-⊡ (stepW ξ₁) (snocR ξ₂ t) = wk₁-⊡ ξ₁ ξ₂

module _
  {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} {{wkVrT : WkVr T}}
  where

  instance
    iCompIdmReg : {{apRelTT : ApRel T T}} {{apIdmTT : ApIdm T T}} → CompIdm (Reg T)
    ⊙-idm {{iCompIdmReg}} (baseR ξ) = refl
    ⊙-idm {{iCompIdmReg}} (snocR ξ t) = cong₂ snocR (⊙-idm {Reg T} ξ) (ap-idm` {T} t)
    idm-⊙ {{iCompIdmReg}} ξ = idm-⊡ {Weaken`} {Reg T} ξ

  lk-⊡ : {{apVr : ApVr T}}
    {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Weaken` γ₁ γ₂) (ξ₂ : Reg T γ₂ γ₃) →
    (i : Ix γ₁) → lk {T} {Reg T} (ξ₁ ⊡ ξ₂) i ≡ ap {T} ξ₂ (lk {T} ξ₁ i)
  lk-⊡ ξ₁ (baseR ξ₂) i = begin
    lk (ξ₁ ⊙ ξ₂) i                           ≡⟨ lk-ren-comp {T} ξ₁ ξ₂ i ⟩
    lk ξ₂ (lk ξ₁ i)                          ≡⟨ sym (ap-vr {T} (baseR ξ₂) (lk ξ₁ i)) ⟩
    ap {T} (baseR ξ₂) (vr (lk  ξ₁ i))        ≡⟨ cong (ap {T} (baseR ξ₂)) (sym (lk-ren {T} ξ₁ i)) ⟩
    ap {T} (baseR ξ₂) (lk ξ₁ i)              ∎
  lk-⊡ baseW ξ₂ i = begin
    lk {T} {Reg T} (baseW ⊡ ξ₂) i             ≡⟨ cong₂ lk (idm-⊡ {Weaken`} ξ₂) refl ⟩
    lk {T} {Reg T} ξ₂ i                      ≡⟨ sym (ap-vr {T} ξ₂ i) ⟩
    ap {T} ξ₂ (vr i)                         ∎
  lk-⊡ (stepW ξ₁) (snocR ξ₂ t) i = begin
    lk {T} {Reg T} (ξ₁ ⊡ ξ₂) i               ≡⟨ lk-⊡ ξ₁ ξ₂ i ⟩
    ap {T} ξ₂ (vr (lk ξ₁ i))                 ≡⟨ ap-vr {T} ξ₂ (lk ξ₁ i) ⟩
    lk ξ₂ (lk ξ₁ i)                          ≡⟨ refl ⟩
    lk (snocR ξ₂ t) (suc (lk ξ₁ i))          ≡⟨ sym (ap-vr {T} (snocR ξ₂ t) (suc (lk ξ₁ i))) ⟩
    ap {T} (snocR ξ₂ t) (vr (suc (lk ξ₁ i))) ∎

  instance
    iLkCompApReg : {{apVr : ApVr T}} → LkCompAp T (Reg T)
    lk-⊙-ap {{iLkCompApReg}} (baseR ξ₁)    ξ₂ i       = lk-⊡ ξ₁ ξ₂ i
    lk-⊙-ap {{iLkCompApReg}} (snocR ξ₁ t) ξ₂ zero    = refl
    lk-⊙-ap {{iLkCompApReg}} (snocR ξ₁ t) ξ₂ (suc i) = lk-⊙-ap {T} ξ₁ ξ₂ i

  wk₁-⊙ : {{apWkTT : ApWk T T}}
    {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Reg T γ₁ γ₂) (ξ₂ : Reg T γ₂ γ₃) →
    wk₁ (ξ₁ ⊙ ξ₂) ≡ wk₁ ξ₁ ⊙ snocR (wk₁ ξ₂) (Vr.vr vrT zero)
  wk₁-⊙ (baseR ξ)     ξ₂ = wk₁-⊡ ξ ξ₂
  wk₁-⊙ (snocR ξ₁ t) ξ₂ = cong₂ snocR (wk₁-⊙ ξ₁ ξ₂) (sym (ap-wk₁ {T} ξ₂ t))

  instance
    iUpCompReg : {{apVrT : ApVr T}} {{apWkTT : ApWk T T}} → UpComp (Reg T)
    ⊙-↑₁ {{iUpCompReg}} ξ₁ ξ₂ = cong₂ snocR
      (wk₁-⊙ ξ₁ ξ₂)
      (sym (ap-vr {T} (snocR (wk₁ ξ₂) (vr zero)) zero))

    iCompAssocReg : {{apVrT : ApVr T}} {{apCompT : ApComp T T}} {{apWkTT : ApWk T T}} →
      CompAssoc (Reg T)
    ⊙-assoc {{iCompAssocReg}} (baseR ξ₁)    ξ₂ ξ₃ = ⊡-⊙-assoc ξ₁ ξ₂ ξ₃
    ⊙-assoc {{iCompAssocReg}} (snocR ξ₁ t) ξ₂ ξ₃ =
      cong₂ snocR (⊙-assoc {Reg T} ξ₁ ξ₂ ξ₃) (ap-⊙ {T} ξ₂ ξ₃ t)

  ⊙-wkm₁-reg : {{apWkmWkTT : ApWkmWk T T}}
    {γ₁ γ₂ : Dom} (ξ : Reg T γ₁ γ₂) →
    ξ ⊙ wkm {Reg T} 1 ≡ wk₁ ξ
  ⊙-wkm₁-reg (baseR ξ)     = refl
  ⊙-wkm₁-reg (snocR ξ t) rewrite sym (wk1-wk₁ t) =
    cong₂ snocR (⊙-wkm₁-reg ξ) (ap-wkm-wk {T} 1 t)

  instance
    iWkmCommReg : {{apVr : ApVr T}} {{apCompT : ApComp T T}} {{apWkTT : ApWk T T}}
      {{apWkmWkTT : ApWkmWk T T}} {{apRelTT : ApRel T T}} {{apIdmTT : ApIdm T T}} →
      WkmComm (Reg T)
    wkm₁-comm {{iWkmCommReg}} (baseR baseW) = refl
    wkm₁-comm {{iWkmCommReg}} (baseR (stepW ξ)) rewrite idm-⊙ {Weaken`} ξ = refl
    wkm₁-comm {{iWkmCommReg}} (snocR ξ t) = ⊙-wkm₁-reg (snocR ξ t)
