
module UniDB.Subst.Subs where

open import UniDB.Subst.Core
open import UniDB.Morph.Subs

--------------------------------------------------------------------------------

module _ {T : STX} {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} where

  instance
    iCompSubs : Comp (Subs T)
    _⊙_ {{iCompSubs}} (refl)      ξ₂          = ξ₂
    _⊙_ {{iCompSubs}} (step ξ₁ t) ξ₂          = step (ξ₁ ⊙ ξ₂) (ap {T} ξ₂ t )
    _⊙_ {{iCompSubs}} (skip ξ₁)   refl        = skip ξ₁
    _⊙_ {{iCompSubs}} (skip ξ₁)   (step ξ₂ t) = step (ξ₁ ⊙ ξ₂) t
    _⊙_ {{iCompSubs}} (skip ξ₁)   (skip ξ₂)   = skip (ξ₁ ⊙ ξ₂)

--------------------------------------------------------------------------------
