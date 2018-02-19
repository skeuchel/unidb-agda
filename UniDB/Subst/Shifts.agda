
module UniDB.Subst.Shifts where

open import UniDB.Subst.Core
open import UniDB.Morph.Shifts

module _ {T : STX} {{vrT : Vr T}} {{apTT : Ap T T}} {{apVrT : ApVr T}} where

  instance
    iLkCompApShifts : LkCompAp T Shifts
    lk-⊙-ap {{iLkCompApShifts}} ξ₁ ξ₂ i = begin
      vr (lk (ξ₁ ⊙ ξ₂) i)     ≡⟨ cong vr (shiftIx-⊙ ξ₁ ξ₂ i) ⟩
      vr (lk ξ₂ (lk ξ₁ i))     ≡⟨ sym (ap-vr {T} ξ₂ (lk ξ₁ i)) ⟩
      ap {T} ξ₂ (vr (lk ξ₁ i)) ∎
