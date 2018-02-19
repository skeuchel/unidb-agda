module UniDB.Morph.StarPrime where

open import UniDB.Spec
open import UniDB.Morph.Depth

mutual
  data Star* (Ξ : MOR) : MOR where
    refl : {γ : Dom} → Star* Ξ γ γ
    incl : {γ₁ γ₂ : Dom} (ξs : Star+ Ξ γ₁ γ₂) → Star* Ξ γ₁ γ₂

  data Star+ (Ξ : MOR) : MOR where
    step : {γ₁ γ₂ γ₃ : Dom} (ξs : Star* Ξ γ₁ γ₂) (ξ : Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃

module _ {Ξ : MOR} where
  mutual
    step` : {Ξ : MOR} {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζs : Star* Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃
    step` ξ refl     = step refl ξ
    step` ξ (incl ζ) = step+ ξ ζ

    step+ : {Ξ : MOR} {γ₁ γ₂ γ₃ : Dom} (ξ : Ξ γ₁ γ₂) (ζs : Star+ Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃
    step+ ξ (step ζs ζ) = step (incl (step` ξ ζs)) ζ

  mutual
    comp** : {γ₁ γ₂ γ₃ : Dom} (ξs : Star* Ξ γ₁ γ₂) (ζs : Star* Ξ γ₂ γ₃) → Star* Ξ γ₁ γ₃
    comp** ξs refl      = ξs
    comp** ξs (incl ζs) = incl (comp*+ ξs ζs)

    comp*+ : {γ₁ γ₂ γ₃ : Dom} (ξs : Star* Ξ γ₁ γ₂) (ζs : Star+ Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃
    comp*+ ξs (step ζs ζ) = step (comp** ξs ζs) ζ

  mutual
    comp+* : {γ₁ γ₂ γ₃ : Dom} (ξs : Star+ Ξ γ₁ γ₂) (ζs : Star* Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃
    comp+* ξs refl      = ξs
    comp+* ξs (incl ζs) = comp++ ξs ζs

    comp++ : {γ₁ γ₂ γ₃ : Dom} (ξs : Star+ Ξ γ₁ γ₂) (ζs : Star+ Ξ γ₂ γ₃) → Star+ Ξ γ₁ γ₃
    comp++ ξs (step ζs ζ) = step (incl (comp+* ξs ζs)) ζ

module _ {Ξ : MOR} {{upΞ : Up Ξ}} where

  mutual
    instance
      iUpStar* : Up (Star* Ξ)
      _↑₁ {{iUpStar*}} refl      = refl
      _↑₁ {{iUpStar*}} (incl ξs) = incl (ξs ↑₁)
      _↑_ {{iUpStar*}} ξ 0 = ξ
      _↑_ {{iUpStar*}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
      ↑-zero {{iUpStar*}} ξ = refl
      ↑-suc {{iUpStar*}} ξ δ⁺ = refl

      iUpStar+ : Up (Star+ Ξ)
      _↑₁ {{iUpStar+}} (step ξs ξ) = step (ξs ↑₁) (ξ ↑₁)
      _↑_ {{iUpStar+}} ξ 0 = ξ
      _↑_ {{iUpStar+}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
      ↑-zero {{iUpStar+}} ξ = refl
      ↑-suc {{iUpStar+}} ξ δ⁺ = refl
