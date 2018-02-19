module UniDB.Spec where

open import UniDB.Core public

record Vr (T : STX) : Set where
  field
    vr     : {γ : Dom} → Ix γ → T γ
    vr-inj : {γ : Dom} → Inj (vr {γ})
open Vr {{...}} public

record Wk (X : STX) : Set where
  field
    wk₁     : {γ : Dom} (x : X γ) → X (suc γ)
    wk      : {γ : Dom} (δ : Dom) (x : X γ) → X (γ ∪ δ)
    wk-zero : {γ : Dom} (x : X γ) → wk 0 x ≡ x
    wk-suc  : {γ : Dom} (δ : Dom) (x : X γ) → wk (suc δ) x ≡ wk₁ (wk δ x)

  wk1-wk₁ : {γ : Dom} (x : X γ) →
    wk 1 x ≡ wk₁ x
  wk1-wk₁ x = trans (wk-suc 0 x) (cong wk₁ (wk-zero x))
open Wk {{...}} public

instance
  iVrIx : Vr Ix
  vr     {{iVrIx}} i = i
  vr-inj {{iVrIx}} p = p

  iWkIx : Wk Ix
  wk₁     {{iWkIx}}           = suc
  wk      {{iWkIx}} zero    i = i
  wk      {{iWkIx}} (suc δ) i = suc (wk δ i)
  wk-zero {{iWkIx}} x         = refl
  wk-suc  {{iWkIx}} δ x       = refl

--------------------------------------------------------------------------------

record WkVr (T : STX) {{vrT : Vr T}} {{wkT : Wk T}} : Set where
  field
    wk₁-vr  : {γ : Dom} (i : Ix γ) →
      wk₁ (vr {T} i) ≡ vr {T} (wk₁ i)
    wk-vr  : {γ : Dom} (δ : Dom) (i : Ix γ) →
      wk δ (vr {T} i) ≡ vr {T} (wk δ i)
open WkVr {{...}} public

instance
  iWkVrIx : WkVr Ix
  wk₁-vr {{iWkVrIx}} i = refl
  wk-vr {{iWkVrIx}} δ i = refl

--------------------------------------------------------------------------------

record Lk (T : STX) (Ξ : MOR) : Set where
  field
    lk : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (i : Ix γ₁) → T γ₂
open Lk {{...}} public

record Up (Ξ : MOR) : Set where
  infixl 9 _↑₁ _↑_
  field
    _↑₁ : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) → Ξ (suc γ₁) (suc γ₂)
    _↑_ : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (δ : Dom) → Ξ (γ₁ ∪ δ) (γ₂ ∪ δ)
    ↑-zero : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) → ξ ↑ zero ≡ ξ
    ↑-suc : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (δ : Dom) → ξ ↑ suc δ ≡ ξ ↑ δ ↑₁

record Comp (Ξ : MOR) : Set where
  infixl 8 _⊙_
  field
    _⊙_ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) → Ξ γ₁ γ₃

record Idm (Ξ : MOR) : Set where
  field
    idm : (γ : Dom) → Ξ γ γ

record Wkm (Ξ : MOR) : Set where
  field
    wkm : {γ : Dom} (δ : Dom) → Ξ γ (γ ∪ δ)

record Snoc (T : STX) (Ξ : MOR) : Set where
  field
    snoc : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (t : T γ₂) → Ξ (suc γ₁) γ₂

record Beta (T : STX) (Ξ : MOR) : Set where
  field
    beta : {γ : Dom} (t : T γ) → Ξ (suc γ) γ

open Idm {{...}} public
open Wkm {{...}} public
open Up {{...}} public
open Comp {{...}} public
open Snoc {{...}} public
open Beta {{...}} public

--------------------------------------------------------------------------------

record LkRen
  (T : STX) {{vrT : Vr T}}
  (Ξ : MOR) {{lkIxΞ : Lk Ix Ξ}} {{lkTΞ : Lk T Ξ}} : Set where
  field
    lk-ren : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (i : Ix γ₁) →
      lk {T} ξ i ≡ vr (lk ξ i)
open LkRen {{...}} public

record LkUp
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} : Set where
  field
    lk-↑₁-zero : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) →
      lk {T} (ξ ↑₁) zero ≡ vr zero
    lk-↑₁-suc : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (i : Ix γ₁) →
      lk {T} (ξ ↑₁) (suc i) ≡ wk₁ (lk ξ i)

  lk-↑-∪ : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (i : Ix γ₁) (δ : Dom) →
    lk {T} (ξ ↑ δ) (wk δ i) ≡ wk δ (lk ξ i)
  lk-↑-∪ ξ i zero    = begin
    lk (ξ ↑ 0) i                  ≡⟨ cong₂ lk ((↑-zero ξ)) refl ⟩
    lk ξ i                        ≡⟨ sym (wk-zero (lk ξ i)) ⟩
    wk 0 (lk ξ i)                 ∎
  lk-↑-∪ ξ i (suc δ) = begin
    lk (ξ ↑ suc δ) (suc (wk δ i)) ≡⟨ cong₂ lk (↑-suc ξ δ) refl ⟩
    lk (ξ ↑ δ ↑₁) (suc (wk δ i))  ≡⟨ lk-↑₁-suc (ξ ↑ δ) (wk δ i) ⟩
    wk₁ (lk (ξ ↑ δ) (wk δ i))     ≡⟨ cong wk₁ (lk-↑-∪ ξ i δ) ⟩
    wk₁ (wk δ (lk ξ i))           ≡⟨ sym (wk-suc δ (lk ξ i)) ⟩
    wk (suc δ) (lk ξ i)           ∎
open LkUp {{...}} public

record LkRenComp
  (T : STX) {{vrT : Vr T}}
  (Ξ : MOR) {{lkIxΞ : Lk Ix Ξ}} {{lkTΞ : Lk T Ξ}} {{compΞ : Comp Ξ}}
  {{lkRenTΞ : LkRen T Ξ}} : Set where
  field
    lk-ren-comp : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃)
      (i : Ix γ₁) → lk {T} (ξ₁ ⊙ ξ₂) i ≡ lk {T} ξ₂ (lk {Ix} ξ₁ i)
open LkRenComp {{...}} public

record LkIdm
  (T : STX) {{vrT : Vr T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{idmΞ : Idm Ξ}} : Set where
  field
    lk-idm : {γ : Dom} (i : Ix γ) → lk {T} (idm {Ξ} γ) i ≡ vr i
open LkIdm {{...}} public

record LkWkm
  (T : STX) {{vrT : Vr T}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{wkmΞ : Wkm Ξ}} : Set where
  field
    lk-wkm : {γ : Dom} (δ : Dom) (i : Ix γ) →
      lk {T} (wkm {Ξ} δ) i ≡ vr (wk δ i)
open LkWkm {{...}} public

--------------------------------------------------------------------------------

record UpIdm (Ξ : MOR) {{upΞ : Up Ξ}} {{idmΞ : Idm Ξ}} : Set where
  field
    idm-↑₁ : {γ : Dom} → idm {Ξ} γ ↑₁ ≡ idm {Ξ} (suc γ)

  idm-↑ : {γ : Dom} (δ : Dom) → idm {Ξ} γ ↑ δ ≡ idm {Ξ} (γ ∪ δ)
  idm-↑ zero    = ↑-zero (idm {Ξ} _)
  idm-↑ (suc δ) = begin
    idm _ ↑ suc δ     ≡⟨ ↑-suc (idm _) δ ⟩
    idm _ ↑ δ ↑₁      ≡⟨ cong _↑₁ (idm-↑ δ) ⟩
    idm _ ↑₁          ≡⟨ idm-↑₁ ⟩
    idm (suc (_ ∪ δ)) ∎
open UpIdm {{...}} public

record UpComp (Ξ : MOR) {{upΞ : Up Ξ}} {{compΞ : Comp Ξ}} : Set where
  field
    ⊙-↑₁ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) →
      (ξ₁ ⊙ ξ₂) ↑₁ ≡ (ξ₁ ↑₁) ⊙ (ξ₂ ↑₁)

  ⊙-↑ : {γ₁ γ₂ γ₃ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) (δ : Dom) →
    (ξ₁ ⊙ ξ₂) ↑ δ ≡ (ξ₁ ↑ δ) ⊙ (ξ₂ ↑ δ)
  ⊙-↑ ξ₁ ξ₂ zero    = begin
    (ξ₁ ⊙ ξ₂) ↑ 0       ≡⟨ ↑-zero (ξ₁ ⊙ ξ₂) ⟩
    ξ₁       ⊙ ξ₂       ≡⟨ sym (cong₂ _⊙_ (↑-zero ξ₁) (↑-zero ξ₂)) ⟩
    (ξ₁ ↑ 0) ⊙ (ξ₂ ↑ 0) ∎
  ⊙-↑ ξ₁ ξ₂ (suc δ) = begin
    (ξ₁ ⊙ ξ₂) ↑ suc δ           ≡⟨ ↑-suc (ξ₁ ⊙ ξ₂) δ ⟩
    (ξ₁ ⊙ ξ₂) ↑ δ ↑₁            ≡⟨ cong _↑₁ (⊙-↑ ξ₁ ξ₂ δ) ⟩
    ((ξ₁ ↑ δ) ⊙ (ξ₂ ↑ δ)) ↑₁    ≡⟨ ⊙-↑₁ (ξ₁ ↑ δ) (ξ₂ ↑ δ) ⟩
    (ξ₁ ↑ δ ↑₁) ⊙ (ξ₂ ↑ δ ↑₁)   ≡⟨ sym (cong₂ _⊙_ (↑-suc ξ₁ δ) (↑-suc ξ₂ δ)) ⟩
    (ξ₁ ↑ suc δ) ⊙ (ξ₂ ↑ suc δ) ∎
open UpComp {{...}} public

record CompIdm (Ξ : MOR) {{idmΞ : Idm Ξ}} {{compΞ : Comp Ξ}} : Set where
  field
    ⊙-idm : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) → ξ ⊙ idm {Ξ} γ₂ ≡ ξ
    idm-⊙ : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) → idm {Ξ} γ₁ ⊙ ξ ≡ ξ
open CompIdm {{...}} public

record CompAssoc (Ξ : MOR) {{compΞ : Comp Ξ}} : Set where
  field
    ⊙-assoc : {γ₁ γ₂ γ₃ γ₄ : Dom} (ξ₁ : Ξ γ₁ γ₂) (ξ₂ : Ξ γ₂ γ₃) (ξ₃ : Ξ γ₃ γ₄) →
      ξ₁ ⊙ (ξ₂ ⊙ ξ₃) ≡ (ξ₁ ⊙ ξ₂) ⊙ ξ₃
open CompAssoc {{...}} public

--------------------------------------------------------------------------------

record WkmBeta
  (T : STX) (Ξ : MOR) {{idmΞ : Idm Ξ}} {{wkmΞ : Wkm Ξ}}
  {{compΞ : Comp Ξ}} {{betaTΞ : Beta T Ξ}} : Set where
  field
    wkm-beta : {γ : Dom} (t : T γ) → wkm {Ξ} 1 ⊙ beta {T} {Ξ} t ≡ idm {Ξ} γ
open WkmBeta {{...}} public

record WkmHom
  (Ξ : MOR) {{idmΞ : Idm Ξ}} {{wkmΞ : Wkm Ξ}} {{compΞ : Comp Ξ}} : Set where
  field
    wkm-zero : {γ : Dom} → wkm {Ξ} 0 ≡ idm {Ξ} γ
    wkm-suc  : {γ : Dom} (δ : Dom) → wkm {Ξ} {γ} (suc δ) ≡ wkm {Ξ} δ ⊙ wkm {Ξ} 1
open WkmHom {{...}} public

record WkmComm
  (Ξ : MOR) {{upΞ : Up Ξ}} {{wkmΞ : Wkm Ξ}} {{compΞ : Comp Ξ}} : Set where
  field
    wkm₁-comm : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) →
      ξ ⊙ wkm {Ξ} 1 ≡ wkm {Ξ} 1 ⊙ ξ ↑₁

  wkm-comm : {{idmΞ : Idm Ξ}} {{wkmHomΞ : WkmHom Ξ}}
    {{compIdmΞ : CompIdm Ξ}} {{compAssocΞ : CompAssoc Ξ}}
    {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (δ : Dom) →
    ξ ⊙ wkm {Ξ} δ ≡ wkm {Ξ} δ ⊙ ξ ↑ δ
  wkm-comm {{iWkmCommReg}} ξ zero  = begin
    ξ ⊙ wkm 0       ≡⟨ cong (_⊙_ ξ) wkm-zero ⟩
    ξ ⊙ idm _       ≡⟨ ⊙-idm ξ ⟩
    ξ               ≡⟨ sym (idm-⊙ ξ) ⟩
    idm _ ⊙ ξ       ≡⟨ sym (cong₂ _⊙_ wkm-zero (↑-zero ξ)) ⟩
    wkm 0 ⊙ (ξ ↑ 0) ∎
  wkm-comm {{iWkmCommReg}} ξ (suc δ) = begin
    ξ ⊙ wkm (suc δ)                ≡⟨ cong (_⊙_ ξ) (wkm-suc δ) ⟩
    ξ ⊙ (wkm δ ⊙ wkm 1)           ≡⟨ ⊙-assoc ξ (wkm δ) (wkm 1) ⟩
    (ξ ⊙ wkm δ) ⊙ wkm 1           ≡⟨ cong (λ ξ → ξ ⊙ wkm 1) (wkm-comm ξ δ) ⟩
    (wkm δ ⊙ (ξ ↑ δ)) ⊙ wkm 1     ≡⟨ sym (⊙-assoc (wkm δ) (ξ ↑ δ) (wkm 1)) ⟩
    wkm δ ⊙ ((ξ ↑ δ) ⊙ wkm 1)     ≡⟨ cong (_⊙_ (wkm δ)) (wkm₁-comm (ξ ↑ δ)) ⟩
    wkm δ ⊙ (wkm 1 ⊙ (ξ ↑ δ ↑₁))  ≡⟨ ⊙-assoc (wkm δ) (wkm 1) (ξ ↑ δ ↑₁) ⟩
    (wkm δ ⊙ wkm 1) ⊙ (ξ ↑ δ ↑₁)  ≡⟨ cong (λ ρ → (wkm δ ⊙ wkm 1) ⊙ ρ) (sym (↑-suc ξ δ)) ⟩
    (wkm δ ⊙ wkm 1) ⊙ (ξ ↑ suc δ) ≡⟨ cong (λ ρ → ρ ⊙ (ξ ↑ suc δ)) (sym (wkm-suc δ)) ⟩
    wkm (suc δ) ⊙ (ξ ↑ suc δ) ∎
open WkmComm {{...}} public

--------------------------------------------------------------------------------

infix 1 [_]_≃_
record [_]_≃_
  (T : STX)
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}}
  {Ζ : MOR} {{lkTΖ : Lk T Ζ}}
  {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂) : Set where
  field
    lk≃ : (i : Ix γ₁) → lk {T} {Ξ} ξ i ≡ lk {T} {Ζ} ζ i
open [_]_≃_ public

module _
  {T : STX} {{vrT : Vr T}} {{wkT : Wk T}}
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}} {{lkUpTΞ : LkUp T Ξ}}
  {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} {{lkUpTΖ : LkUp T Ζ}}
  where

  ≃-↑₁ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : [ T ] ξ ≃ ζ) → [ T ] ξ ↑₁ ≃ ζ ↑₁
  lk≃ (≃-↑₁ {γ₁} {γ₂} {ξ} {ζ} hyp) zero = begin
    lk (ξ ↑₁) zero     ≡⟨ lk-↑₁-zero ξ ⟩
    vr zero            ≡⟨ sym (lk-↑₁-zero ζ) ⟩
    lk (ζ ↑₁) zero     ∎
  lk≃ (≃-↑₁ {γ₁} {γ₂} {ξ} {ζ} hyp) (suc i) = begin
    lk (ξ ↑₁) (suc i)  ≡⟨ lk-↑₁-suc ξ i ⟩
    wk₁ (lk ξ i)       ≡⟨ cong wk₁ (lk≃ hyp i) ⟩
    wk₁ (lk ζ i)       ≡⟨ sym (lk-↑₁-suc ζ i) ⟩
    lk (ζ ↑₁) (suc i)  ∎

  ≃-↑ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : [ T ] ξ ≃ ζ) (δ : Dom) → [ T ] ξ ↑ δ ≃ ζ ↑ δ
  ≃-↑ {ξ = ξ} {ζ} hyp zero
    rewrite ↑-zero {Ξ} ξ | ↑-zero {Ζ} ζ = hyp
  ≃-↑ {ξ = ξ} {ζ} hyp (suc δ)
    rewrite ↑-suc {Ξ} ξ δ | ↑-suc {Ζ} ζ δ = ≃-↑₁ (≃-↑ hyp δ)

--------------------------------------------------------------------------------

infix 1 [_]_≅_
data [_]_≅_ (T : STX)
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
  {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} :
  {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂) → Set where
  ≃-to-≅ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : (δ' : Dom) → [ T ] ξ ↑ δ' ≃ ζ ↑ δ') (δ : Dom) →
    [ T ] ξ ↑ δ ≅ ζ ↑ δ

module _
  {T : STX}
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
  {Ζ : MOR} {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}} where

  ≃-to-≅` : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : (δ' : Dom) → [ T ] ξ ↑ δ' ≃ ζ ↑ δ') → [ T ] ξ ≅ ζ
  ≃-to-≅` {ξ = ξ} {ζ} hyp = lem₂
    where
      lem : [ T ] ξ ↑ 0 ≅ ζ ↑ 0
      lem = ≃-to-≅ hyp 0
      lem₂ : [ T ] ξ ≅ ζ
      lem₂ rewrite sym (↑-zero {Ξ} ξ) | sym (↑-zero {Ζ} ζ) = lem

  ≅-to-≃ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : [ T ] ξ ≅ ζ) → [ T ] ξ ≃ ζ
  ≅-to-≃ (≃-to-≅ hyp δ) = hyp δ

  ≅-↑₁ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : [ T ] ξ ≅ ζ) → [ T ] ξ ↑₁ ≅ ζ ↑₁
  ≅-↑₁ (≃-to-≅ {ξ = ξ} {ζ} hyp δ)
    rewrite sym (↑-suc {Ξ} ξ δ) | sym (↑-suc {Ζ} ζ δ)
    = ≃-to-≅ hyp (suc δ)

  ≅-↑ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂}
    (hyp : [ T ] ξ ≅ ζ) (δ : Dom) → [ T ] ξ ↑ δ ≅ ζ ↑ δ
  ≅-↑ {ξ = ξ} {ζ} hyp zero
    rewrite ↑-zero ξ | ↑-zero ζ
    = hyp
  ≅-↑ {ξ = ξ} {ζ} hyp (suc δ)
    rewrite ↑-suc ξ δ | ↑-suc ζ δ
    = ≅-↑₁ (≅-↑ hyp δ)

module _
  {T : STX} {{vrT : Vr T}}
  {Ξ : MOR} {{lkIxΞ : Lk Ix Ξ}} {{lkTΞ : Lk T Ξ}} {{lkRenTΞ : LkRen T Ξ}} {{upΞ : Up Ξ}}
  {Ζ : MOR} {{lkIxΖ : Lk Ix Ζ}} {{lkTΖ : Lk T Ζ}} {{lkRenTΖ : LkRen T Ζ}} {{upΖ : Up Ζ}} where

  Ix≅-to-≅ : {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} → [ Ix ] ξ ≅ ζ → [ T ] ξ ≅ ζ
  Ix≅-to-≅ (≃-to-≅ {ξ = ξ} {ζ} hyp δ) = ≃-to-≅ (λ δ' → record { lk≃ = λ i → begin
    lk {T} (ξ ↑ δ') i       ≡⟨ lk-ren {T} {Ξ} (ξ ↑ δ') i ⟩
    vr (lk {Ix} (ξ ↑ δ') i) ≡⟨ cong vr (lk≃ (hyp δ') i) ⟩
    vr (lk {Ix} (ζ ↑ δ') i) ≡⟨ sym (lk-ren {T} {Ζ} (ζ ↑ δ') i) ⟩
    lk {T} (ζ ↑ δ') i ∎}) δ

--------------------------------------------------------------------------------

record HComp (Ξ Ζ Θ : MOR) : Set where
  infixl 8 _⊡_
  field
    _⊡_ : {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) → Θ γ₁ γ₃
open HComp {{...}} public

record UpHComp
  (Ξ : MOR) {{upΞ : Up Ξ}}
  (Ζ : MOR) {{upΖ : Up Ζ}}
  (Θ : MOR) {{upΘ : Up Θ}}
  {{hcompΞΖΘ : HComp Ξ Ζ Θ}} : Set where

  field
    ⊡-↑₁ : {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) →
      (_⊡_ {Θ = Θ} ξ ζ) ↑₁ ≡ (ξ ↑₁) ⊡ (ζ ↑₁)

  ⊡-↑ : {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) (δ : Dom) →
    _↑_ {Θ} (ξ ⊡ ζ) δ ≡ (ξ ↑ δ) ⊡ (ζ ↑ δ)
  ⊡-↑ ξ ζ zero = begin
    (ξ ⊡ ζ) ↑ 0           ≡⟨ ↑-zero {Θ} (_⊡_ {Ξ} {Ζ} {Θ} ξ ζ) ⟩
    (ξ ⊡ ζ)               ≡⟨ sym (cong₂ (_⊡_ {Ξ} {Ζ} {Θ}) (↑-zero ξ) (↑-zero ζ)) ⟩
    (ξ ↑ 0) ⊡ (ζ ↑ 0)     ∎
  ⊡-↑ ξ ζ (suc δ) = begin
    (ξ ⊡ ζ) ↑ suc δ       ≡⟨ ↑-suc (ξ ⊡ ζ) δ ⟩
    (ξ ⊡ ζ) ↑ δ ↑₁        ≡⟨ cong _↑₁ ((⊡-↑ ξ ζ δ)) ⟩
    (ξ ↑ δ ⊡ ζ ↑ δ) ↑₁    ≡⟨ ⊡-↑₁ (ξ ↑ δ) (ζ ↑ δ) ⟩
    ξ ↑ δ ↑₁ ⊡ ζ ↑ δ ↑₁   ≡⟨ sym (cong₂ (_⊡_ {Ξ} {Ζ} {Θ}) (↑-suc ξ δ) (↑-suc ζ δ)) ⟩
    ξ ↑ suc δ ⊡ ζ ↑ suc δ ∎
open UpHComp {{...}} public

record HCompIdmLeft
  (Ξ : MOR) {{idmΞ : Idm Ξ}}
  (Ζ : MOR) {{hcompΞΖΖ : HComp Ξ Ζ Ζ}} : Set where
  field
    idm-⊡ : {γ₁ γ₂ : Dom} (ζ : Ζ γ₁ γ₂) → idm {Ξ} γ₁ ⊡ ζ ≡ ζ
open HCompIdmLeft {{...}} public
