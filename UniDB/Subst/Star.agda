
module UniDB.Subst.Star where

open import UniDB.Subst.Core
open import UniDB.Morph.Star

module _
  {T : STX} {{vrT : Vr T}} {{apTT : Ap T T}}
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}} {{upΞ : Up Ξ}}
  where

  instance
    iLkStar : Lk T (Star Ξ)
    lk {{iLkStar}} ε        i = vr i
    lk {{iLkStar}} (ξs ▻ ξ) i = ap {T} ξ (lk ξs i)

    iLkIdmStar : LkIdm T (Star Ξ)
    lk-idm {{iLkIdmStar}} i = refl

    -- iLkCompApStar : {{apIdmT : ApIdm T T}} → LkCompAp T (Star Ξ)
    -- lk-⊙-ap {{iLkCompApStar}} ξs ε        i = sym (ap-idm T T (Star Ξ) (lk T (Star Ξ) ξs i))
    -- lk-⊙-ap {{iLkCompApStar}} ξs (ζs ▻ ζ) i =
    --   begin
    --     ap T T Ξ ζ (lk T (Star Ξ) (ξs ⊙ ζs) i)
    --   ≡⟨ cong (ap T T Ξ ζ) (lk-⊙-ap T (Star Ξ) ξs ζs i) ⟩
    --     ap T T Ξ ζ (ap T T (Star Ξ) ζs (lk T (Star Ξ) ξs i))
    --   ≡⟨ {!!} ⟩
    --     ap T T (Star Ξ) (ζs ▻ ζ) (lk T (Star Ξ) ξs i)
    --   ∎
