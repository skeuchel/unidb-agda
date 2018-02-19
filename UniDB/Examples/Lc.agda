
module UniDB.Examples.Lc where

open import UniDB

data Tm (γ : Dom) : Set where
  var : (i : Ix γ) → Tm γ
  abs : (t : Tm (suc γ)) → Tm γ
  app : (t₁ t₂ : Tm γ) → Tm γ

instance
  iVrTm : Vr Tm
  vr     {{iVrTm}}      = var
  vr-inj {{iVrTm}} refl = refl

  iApTm : Ap Tm Tm
  ap {{iApTm}} ξ (var i)    = lk ξ i
  ap {{iApTm}} ξ (abs t)    = abs (ap {Tm} (ξ ↑₁) t )
  ap {{iApTm}} ξ (app t t₁) = app (ap {Tm} ξ t) (ap {Tm} ξ t₁)

  iApVrTm : ApVr Tm
  ap-vr {{iApVrTm}} ξ i = refl

  iApIdmTm : ApIdm Tm Tm
  ap-idm {{iApIdmTm}} {Ξ} (var i)    = lk-idm {Tm} {Ξ} i
  ap-idm {{iApIdmTm}} {Ξ} (abs t)    = cong abs (begin
    ap {Tm} (idm {Ξ} _ ↑₁) t  ≡⟨ cong₂ (ap {Tm}) (idm-↑₁ {Ξ}) (refl {x = t}) ⟩
    ap {Tm} (idm {Ξ} _) t     ≡⟨ ap-idm {Tm} t ⟩
    t                         ∎)
  ap-idm {{iApIdmTm}} {Ξ} (app t t₁) =
    cong₂ app (ap-idm {Tm} t) (ap-idm {Tm} t₁)

  iApPairTm : ApPair Tm Tm
  ap-pair {{iApPairTm}} ξ ζ (var i)     = refl
  ap-pair {{iApPairTm}} ξ ζ (abs x)     = cong abs (ap-pair {Tm} (ξ ↑₁) (ζ ↑₁) x)
  ap-pair {{iApPairTm}} ξ ζ (app x₁ x₂) = cong₂ app (ap-pair {Tm} ξ ζ x₁) (ap-pair {Tm} ξ ζ x₂)

  iApRelTm : ApRel Tm Tm
  ap-rel≅ {{iApRelTm}} hyp (var i)     = lk≃ (≅-to-≃ hyp) i
  ap-rel≅ {{iApRelTm}} hyp (abs t)     = cong abs (ap-rel≅ {Tm} {Tm} (≅-↑₁ hyp) t)
  ap-rel≅ {{iApRelTm}} hyp (app t₁ t₂) = cong₂ app (ap-rel≅ {Tm} {Tm} hyp t₁) (ap-rel≅ {Tm} {Tm} hyp t₂)

postulate
  Ρ : MOR
  instance
    iIdmΡ : Idm Ρ
    iWkmΡ : Wkm Ρ
    iUpΡ : Up Ρ
    iUpIdmΡ : UpIdm Ρ
    iCompΡ : Comp Ρ
    iWkmHomΡ : WkmHom Ρ
    iLkΡ : {T : STX} {{vrT : Vr T}} → Lk T Ρ
    iLkIdmΡ : {T : STX} {{vrT : Vr T}} → LkIdm T Ρ
    iLkWkmΡ : {T : STX} {{vrT : Vr T}} → LkWkm T Ρ
    iLkCompAp : {T : STX} {{vrT : Vr T}} {{apTT : Ap T T}} {{apVrT : ApVr T}} → LkCompAp T Ρ
    iLkUpΡ : {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} → LkUp T Ρ
    iLkRenΡ : {T : STX} {{vrT : Vr T}} → LkRen T Ρ

instance
  iWkTm : Wk Tm
  wk₁ {{iWkTm}} = ap {Tm} (wkm {Ρ} 1)
  wk {{iWkTm}} δ t = ap {Tm} (wkm {Ρ} δ) t
  wk-zero {{iWkTm}} t = begin
    ap {Tm} (wkm {Ρ} 0) t ≡⟨ ap-rel≅ {Tm} (Ix≅-to-≅ {Tm} (≃-to-≅` (≃-↑ {Ix} (record { lk≃ = λ i → begin
        lk (wkm {Ρ} 0) i ≡⟨ lk-wkm {Ix} {Ρ} 0 i ⟩
        i                ≡⟨ sym (lk-idm {Ix} {Ρ} i) ⟩
        lk (idm {Ρ} _) i ∎
      })))) t ⟩
    ap {Tm} (idm {Ρ} _) t ≡⟨ ap-idm {Tm} {Tm} {Ρ} t ⟩
    t                     ∎
  wk-suc {{iWkTm}} δ t = begin
    ap {Tm} (wkm {Ρ} (suc δ)) t                 ≡⟨ cong (λ ζ → ap {Tm} {Tm} {Ρ} ζ t) (wkm-suc {Ρ} δ) ⟩
    ap {Tm} (wkm {Ρ} δ ⊙ wkm {Ρ} 1) t          ≡⟨ ap-rel≅ {Tm} (Ix≅-to-≅ {Tm} {Ρ} {Pair Ρ Ρ} (≃-to-≅`
      (≃-↑ {Ix} {Ρ} {Pair Ρ Ρ} {ξ = wkm {Ρ} δ ⊙ wkm {Ρ} 1} {wkm {Ρ} δ ⊗ wkm {Ρ} 1} (record { lk≃ =
        lk-⊙-ap {Ix} {Ρ} (wkm {Ρ} δ) (wkm {Ρ} 1)  })))) t ⟩
    ap {Tm} (wkm {Ρ} δ ⊗ wkm {Ρ} 1) t          ≡⟨ ap-pair {Tm} (wkm {Ρ} δ) (wkm {Ρ} 1) t ⟩
    ap {Tm} (wkm {Ρ} 1) (ap {Tm} (wkm {Ρ} δ) t) ∎

instance
  iWkVrTm : WkVr Tm
  wk₁-vr {{iWkVrTm}} i = lk-wkm {Tm} {Ρ} 1 i
  wk-vr {{iWkVrTm}} δ i = lk-wkm {Tm} {Ρ} δ i

  iApWkmWkTm : ApWkmWk Tm Tm
  ap-wkm-wk₁ {{iApWkmWkTm}} {Ξ} = ap-wkm-rel Tm Tm Ξ Ρ 1
  ap-wkm-wk {{iApWkmWkTm}} {Ξ} = ap-wkm-rel Tm Tm Ξ Ρ

  -- iApCompTm : ApComp Tm Tm
  -- ap-⊙ {{iApCompTm}} {Ξ} ξ₁ ξ₂ (var i) = lk-⊙-ap {Tm} {Ξ} ξ₁ ξ₂ i
  -- ap-⊙ {{iApCompTm}} {Ξ} ξ₁ ξ₂ (abs t) rewrite ⊙-↑₁ {Ξ} ξ₁ ξ₂ =
  --   cong abs (ap-⊙ {Tm} (ξ₁ ↑₁) (ξ₂ ↑₁) t)
  -- ap-⊙ {{iApCompTm}} {Ξ} ξ₁ ξ₂ (app t₁ t₂) =
  --   cong₂ app (ap-⊙ {Tm} {Tm} {Ξ} ξ₁ ξ₂ t₁) (ap-⊙ {Tm} {Tm} {Ξ} ξ₁ ξ₂ t₂)

  iApCompTm : ApComp Tm Tm
  iApCompTm = iApComp Tm Tm

  iApWkTm : ApWk Tm Tm
  iApWkTm = iApWk Tm Tm

{-}



--------------------------------------------------------------------------------

subTm : {X : STX} {{apTmX : Ap Tm X}} {γ : Dom} (s : Tm γ) (x : X (suc γ)) → X γ
subTm {X} s x = ap Tm X (Sub Tm) (beta Tm (Sub Tm) s) x

data Eval {γ : Dom} : Tm γ → Tm γ → Set where
  e-app₁ : {t₁ t₁' t₂ : Tm γ} → Eval t₁ t₁' → Eval (app t₁ t₂) (app t₁' t₂)
  e-app₂ : {t₁ t₂ t₂' : Tm γ} → Eval t₂ t₂' → Eval (app t₁ t₂) (app t₁ t₂')
  e-abs  : {t t' : Tm (suc γ)} → Eval t t' → Eval (abs t) (abs t')
  e-beta : {s : Tm γ} {t : Tm (suc γ)} → Eval (app (abs t) s) (subTm s t)

--------------------------------------------------------------------------------
-}
