
module UniDB.Subst.StarPrime where

open import UniDB.Subst.Core
open import UniDB.Morph.StarPrime
open import UniDB.Morph.Depth

module _
  {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}}
  {Ξ : MOR} {{lkTΞ : Lk T Ξ}}
  where

  mutual
    instance
      iLkStar* : Lk T (Star* Ξ)
      lk {{iLkStar*}} refl     i = vr i
      lk {{iLkStar*}} (incl ξ) i = lk ξ i

      iLkStar₁ : Lk T (Star+ Ξ)
      lk {{iLkStar₁}} (step ξs ξ) i = ap {T} (depth ξ 0) (lk ξs i)
