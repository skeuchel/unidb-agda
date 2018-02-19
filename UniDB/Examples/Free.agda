{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}

module UniDB.Examples.Free where

open import UniDB
open import Function
open import Relation.Binary.PropositionalEquality
import Level

-- Interpret a value of the morphism representation Ξ as
-- a morphism between S and T.
Int : (Ξ : MOR) (S T : STX) → Set
Int Ξ S T = (γ₁ γ₂ : Dom) (ξ : Ξ γ₁ γ₂) → S γ₁ → T γ₂

-- Combine two types and their interpretations to an
-- intepretation of an outer composition.
IntPair : (Ξ Ζ : MOR) (S T U : STX) →
  (intΞ : Int Ξ S T) (intΖ : Int Ζ T U) →
  Int (Pair Ξ Ζ) S U
IntPair Ξ Ζ S T U intΞ intΖ _ _ (ξ ⊗ ζ) = intΖ _ _ ζ ∘ intΞ _ _ ξ

-- Predicate: The interpretation of an identity morphism is
-- indeed an identity.
IntIdm : (Ξ : MOR) (T : STX) {{idmΞ : Idm Ξ}} (intΞ : Int Ξ T T) → Set
IntIdm Ξ T intΞ = (γ : Dom) (t : T γ) → intΞ _ _ (idm {Ξ} γ) t ≡ t

-- Pointwise equality between two differently represented morphisms.
_∣_⊢_≃_ :
  {Ξ Ζ : MOR} {S T : STX} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  (intΞ : Int Ξ S T) (intΖ : Int Ζ S T)
  {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂) → Set
intΞ ∣ intΖ ⊢ ξ ≃ ζ = ∀ s → intΞ _ _ ξ s ≡ intΖ _ _ ζ s

-- Equality at arbitrary depths
data _∣_⊢_≅_
  {Ξ Ζ : MOR} {S T : STX} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  (intΞ : Int Ξ S T) (intΖ : Int Ζ S T) :
  {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂) → Set where
  ≃-to-≅ :
    {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂)
    (δ : Dom) (eq≃ : (δ' : Dom) → intΞ ∣ intΖ ⊢ (ξ ↑ δ') ≃ (ζ ↑ δ')) →
    intΞ ∣ intΖ ⊢ (ξ ↑ δ) ≅ (ζ ↑ δ)

-- ≅ can always be pushed under binders
int≅-↑₁ :
  {Ξ Ζ : MOR} {S T : STX} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  {intΞ : Int Ξ S T} {intΖ : Int Ζ S T}
  {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} →
  intΞ ∣ intΖ ⊢ ξ ≅ ζ →
  intΞ ∣ intΖ ⊢ (ξ ↑₁) ≅ (ζ ↑₁)
int≅-↑₁ (≃-to-≅ ξ ζ δ eq≃) rewrite sym (↑-suc ξ δ) | sym (↑-suc ζ δ) =
  ≃-to-≅ ξ ζ (suc δ) eq≃

int≅-↑ :
  {Ξ Ζ : MOR} {S T : STX} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  {intΞ : Int Ξ S T} {intΖ : Int Ζ S T}
  {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} →
  intΞ ∣ intΖ ⊢ ξ ≅ ζ →
  (δ : Dom) → intΞ ∣ intΖ ⊢ (ξ ↑ δ) ≅ (ζ ↑ δ)
int≅-↑ {ξ = ξ} {ζ} eq zero    rewrite ↑-zero ξ  | ↑-zero ζ  = eq
int≅-↑ {ξ = ξ} {ζ} eq (suc δ) rewrite ↑-suc ξ δ | ↑-suc ζ δ = int≅-↑₁ (int≅-↑ eq δ)

lk≅ :
  {Ξ Ζ : MOR} {S T : STX} {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  {intΞ : Int Ξ S T} {intΖ : Int Ζ S T}
  {γ₁ γ₂ : Dom} {ξ : Ξ γ₁ γ₂} {ζ : Ζ γ₁ γ₂} →
  intΞ ∣ intΖ ⊢ ξ ≅ ζ →
  ∀ s → intΞ _ _ ξ s ≡ intΖ _ _ ζ s
lk≅ (≃-to-≅ ξ ζ δ eq≃) s = eq≃ δ s

record Functor (F : STX → STX) : Set₁ where
  field
    fmap :
      (Ξ : MOR) (S T : STX) {{up : Up Ξ}} (intΞ : Int Ξ S T) →
      (γ₁ γ₂ : Dom) (ξ : Ξ γ₁ γ₂) → F S γ₁ → F T γ₂
    fmap-idm :
      (Ξ : MOR) (T : STX) {{upΞ : Up Ξ}} {{idmΞ : Idm Ξ}}
      (intΞ : Int Ξ T T) (intIdmΞ : IntIdm Ξ T intΞ)
      (γ : Dom) (ft : F T γ) →
      fmap Ξ T T intΞ _ _ (idm {Ξ} γ) ft ≡ ft
    fmap-⊗ :
      (Ξ Ζ : MOR) (S T U : STX) {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
      (intΞ : Int Ξ S T) (intΖ : Int Ζ T U)
      (γ₁ γ₂ γ₃ : Dom) (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) (fs : F S γ₁) →
      fmap (Pair Ξ Ζ) S U (IntPair Ξ Ζ S T U intΞ intΖ) _ _ (ξ ⊗ ζ) fs ≡
      fmap Ζ T U intΖ _ _ ζ (fmap Ξ S T intΞ _ _ ξ fs)
    fmap-≅ :
      (Ξ Ζ : MOR) (S T : STX) {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
      (intΞ : Int Ξ S T) (intΖ : Int Ζ S T)
      (γ₁ γ₂ : Dom) (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₁ γ₂) →
      intΞ ∣ intΖ ⊢ ξ ≅ ζ  →
      fmap Ξ S T intΞ ∣ fmap Ζ S T intΖ ⊢ ξ ≅ ζ
open Functor {{...}}

--------------------------------------------------------------------------------
-- Freely generated functor

data Free (F : STX → STX) (V : STX) (γ : Dom) : Set where
  var  : (i : V γ) → Free F V γ
  free : F (Free F V) γ → Free F V γ

bind :
  (F : STX → STX) {{functorF : Functor F}}
  (V W : STX) (Ξ : MOR) {{upΞ : Up Ξ}}
  (intΞ : (γ₁ γ₂ : Dom) → Ξ γ₁ γ₂ → V γ₁ → Free F W γ₂) →
  (γ₁ γ₂ : Dom) → Free F V γ₁ → Ξ γ₁ γ₂ → Free F W γ₂
bind F V W Ξ intΞ γ₁ γ₂ (var v)    ξ = intΞ γ₁ γ₂ ξ v
bind F V W Ξ intΞ γ₁ γ₂ (free ffv) ξ =
  free (fmap {F} Ξ (Free F V) (Free F W)
          (λ γ₃ γ₄ ξ' x' → bind F V W Ξ intΞ γ₃ γ₄ x' ξ' )
          γ₁ γ₂ ξ ffv)

--------------------------------------------------------------------------------
-- Functor instance for Free F

postulate
  ext : Extensionality Level.zero Level.zero

fmap-intpair :
  (F : STX → STX) {{_ : Functor F}}
  (Ξ Ζ : MOR) (S T U : STX) {{upΞ : Up Ξ}} {{upΖ : Up Ζ}}
  (intΞ : Int Ξ S T) (intΖ : Int Ζ T U) →
  fmap {F} (Pair Ξ Ζ) S U (IntPair Ξ Ζ S T U intΞ intΖ) ≡
  IntPair Ξ Ζ (F S) (F T) (F U) (fmap {F} Ξ S T intΞ) (fmap {F} Ζ T U intΖ)
fmap-intpair F Ξ Ζ S T U intΞ intΖ =
  ext λ γ₁ → ext λ γ₃ → ext λ { (_⊗_ {._} {γ₂} ξ ζ) → ext λ fs →
    fmap-⊗ {F} Ξ Ζ S T U intΞ intΖ γ₁ γ₂ γ₃ ξ ζ fs }

instance
  iFunctorFree : {F : STX → STX} {{functorF : Functor F}} →
    Functor (Free F)
  fmap {{iFunctorFree {F}}} Ξ S T intΞ _ _ ξ (var s) = var (intΞ _ _ ξ s)
  fmap {{iFunctorFree {F}}} Ξ S T intΞ _ _ ξ (free x) =
    free (fmap Ξ (Free F S) (Free F T) (fmap Ξ S T intΞ) _ _ ξ x)
  fmap-idm {{iFunctorFree {F}}} Ξ T intΞ intIdmΞ _ (var t)    = cong var (intIdmΞ _ t)
  fmap-idm {{iFunctorFree {F}}} Ξ T intΞ intIdmΞ _ (free fft) = cong free
    (fmap-idm {F} Ξ (Free F T) (fmap Ξ T T intΞ) (fmap-idm {Free F} Ξ T intΞ intIdmΞ) _ fft)
  fmap-⊗ {{iFunctorFree {F}}} Ξ Ζ S T U intΞ intΖ _ _ _ ξ ζ (var i) = cong var refl
  fmap-⊗ {{iFunctorFree {F}}} Ξ Ζ S T U intΞ intΖ _ _ _ ξ ζ (free x) = cong free (begin
    fmap (Pair Ξ Ζ) (Free F S) (Free F U) (fmap (Pair Ξ Ζ) S U (IntPair Ξ Ζ S T U intΞ intΖ)) _ _ (ξ ⊗ ζ) x
      ≡⟨ cong
           (λ (int : Int (Pair Ξ Ζ) (Free F S) (Free F U)) →
              fmap (Pair Ξ Ζ) (Free F S) (Free F U) int _ _ (ξ ⊗ ζ) x)
           (fmap-intpair (Free F) Ξ Ζ S T U intΞ intΖ)
       ⟩
    fmap (Pair Ξ Ζ) (Free F S) (Free F U) (IntPair Ξ Ζ (Free F S) (Free F T) (Free F U) (fmap Ξ S T intΞ) (fmap Ζ T U intΖ)) _ _ (ξ ⊗ ζ) x
      ≡⟨ fmap-⊗ {F} Ξ Ζ (Free F S) (Free F T) (Free F U) (fmap Ξ S T intΞ) (fmap Ζ T U intΖ) _ _ _ ξ ζ x ⟩
    fmap Ζ (Free F T) (Free F U) (fmap Ζ T U intΖ) _ _ ζ (fmap Ξ (Free F S) (Free F T) (fmap Ξ S T intΞ) _ _ ξ x)
      ∎)
  fmap-≅ {{iFunctorFree {F}}} Ξ Ζ S T intΞ intΖ _ _ _ _ eq = {!!}

--------------------------------------------------------------------------------
-- Specialiation to monads relative on Ix

module _ {F : STX → STX} {{functorF : Functor F}} where
  instance
    iVrFree : Vr (Free F Ix)
    vr     {{iVrFree}}      = var
    vr-inj {{iVrFree}} refl = refl

    iApFree : Ap (Free F Ix) (Free F Ix)
    ap {{iApFree}} {Ξ} ξ x = bind F Ix Ix Ξ (λ _ _ → lk) _ _ x ξ

    iApVrFree : ApVr (Free F Ix)
    ap-vr {{iApVrFree}} ξ i = refl

    -- After proving these three properties the relative monad laws
    -- can be derived from the library.
    iApIdmFree : ApIdm (Free F Ix) (Free F Ix)
    ap-idm {{iApIdmFree}} {Ξ} x = {!!}

    iApPairFree : ApPair (Free F Ix) (Free F Ix)
    ap-pair {{iApPairFree}} ξ ζ x = {!!}

    iApRelFree : ApRel (Free F Ix) (Free F Ix)
    ap-rel≅ {{iApRelFree}} eq x = {!!}
