module UniDB.Subst.Sum where

open import UniDB.Subst.Core
open import UniDB.Morph.Sum

--------------------------------------------------------------------------------

module _
  (T : STX) {{vrT : Vr T}} {{wkT : Wk T}}
  (X : STX) {{wkX : Wk X}} {{apTX : Ap T X}} {{apRelTX : ApRel T X}}
  (Ξ : MOR) {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
  (Ζ : MOR) {{lkTΖ : Lk T Ζ}} {{upΖ : Up Ζ}}
  where

  ap-inl : {γ₁ γ₂ : Dom} (ξ : Ξ γ₁ γ₂) (x : X γ₁) →
    ap {T} {X} {Sum Ξ Ζ} (inl ξ) x ≡ ap {T} ξ x
  ap-inl ξ = ap-rel≅ {T} (≃-to-≅` lem)
    where
      lem : (δ : Dom) → [ T ] inl {Ξ} {Ζ} ξ ↑ δ ≃ ξ ↑ δ
      lk≃ (lem δ) i rewrite inl-↑ Ξ Ζ ξ δ = refl

  ap-inr : {γ₁ γ₂ : Dom} (ζ : Ζ γ₁ γ₂) (x : X γ₁) →
    ap {T} {X} {Sum Ξ Ζ} (inr ζ) x ≡ ap {T} ζ x
  ap-inr ζ = ap-rel≅ {T} (≃-to-≅` lem)
    where
      lem : (δ : Dom) → [ T ] inr {Ξ} {Ζ} ζ ↑ δ ≃ ζ ↑ δ
      lk≃ (lem δ) i rewrite inr-↑ Ξ Ζ ζ δ = refl

--------------------------------------------------------------------------------
