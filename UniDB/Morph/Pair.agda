
module UniDB.Morph.Pair where

open import UniDB.Spec

--------------------------------------------------------------------------------

infixl 5 _⊗_
data Pair (Ξ Ζ : MOR) : MOR where
  _⊗_ : {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζ : Ζ γ₂ γ₃) →
    Pair Ξ Ζ γ₁ γ₃

instance
  iHCompPair : {Ξ Ζ : MOR} → HComp Ξ Ζ (Pair Ξ Ζ)
  _⊡_ {{iHCompPair}} = _⊗_

module _
  {Ξ : MOR} {{upΞ : Up Ξ}}
  {Ζ : MOR} {{upΖ : Up Ζ}}
  where

  instance
    iUpPair : Up (Pair Ξ Ζ)
    _↑₁ {{iUpPair}} (ξ ⊗ ζ) = ξ ↑₁ ⊗ ζ ↑₁
    _↑_ {{iUpPair}} (ξ ⊗ ζ) δ = (ξ ↑ δ) ⊗ (ζ ↑ δ)
    ↑-zero {{iUpPair}} (ξ ⊗ ζ) rewrite ↑-zero ξ | ↑-zero ζ = refl
    ↑-suc {{iUpPair}} (ξ ⊗ ζ) δ⁺ rewrite ↑-suc ξ δ⁺ | ↑-suc ζ δ⁺ = refl

    iUpHCompPair : UpHComp Ξ Ζ (Pair Ξ Ζ)
    ⊡-↑₁ {{iUpHCompPair}} ξ ζ = refl

--------------------------------------------------------------------------------
