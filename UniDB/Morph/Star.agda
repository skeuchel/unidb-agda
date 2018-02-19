
module UniDB.Morph.Star where

open import UniDB.Spec

infixl 4 _▻_
data Star (Ξ : MOR) : MOR where
  ε   : {γ : Dom} → Star Ξ γ γ
  _▻_ : {γ₁ γ₂ γ₃ : Dom} (ξs : Star Ξ γ₁ γ₂) (ξ : Ξ γ₂ γ₃) → Star Ξ γ₁ γ₃

module _ {Ξ : MOR} where
  instance
    iIdmStar : Idm (Star Ξ)
    idm {{iIdmStar}} _ = ε

    iCompStar : Comp (Star Ξ)
    _⊙_ {{iCompStar}} ξs ε = ξs
    _⊙_ {{iCompStar}} ξs (ζs ▻ ζ) = (ξs ⊙ ζs) ▻ ζ

module _ {Ξ : MOR} {{upΞ : Up Ξ}} where

  instance
    iUpStar : Up (Star Ξ)
    _↑₁ {{iUpStar}} ε        = ε
    _↑₁ {{iUpStar}} (ξs ▻ ξ) = (ξs ↑₁) ▻ (ξ ↑₁)
    _↑_ {{iUpStar}} ξ 0 = ξ
    _↑_ {{iUpStar}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
    ↑-zero {{iUpStar}} ξ = refl
    ↑-suc {{iUpStar}} ξ δ⁺ = refl

    iUpIdmStar : UpIdm (Star Ξ)
    idm-↑₁ {{iUpIdmStar}} = refl

    iUpCompStar : UpComp (Star Ξ)
    ⊙-↑₁ {{iUpCompStar}} ξs ε        = refl
    ⊙-↑₁ {{iUpCompStar}} ξs (ζs ▻ ζ) =
      cong₂ _▻_ (⊙-↑₁ {Star Ξ} ξs ζs ) (refl {x = ζ ↑₁})
