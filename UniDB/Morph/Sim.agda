
module UniDB.Morph.Sim where

open import UniDB.Spec
open import UniDB.Subst.Core
open import UniDB.Morph.Depth
import Level
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

record Sim (T : STX) (γ₁ γ₂ : Dom) : Set where
  constructor sim
  field
    lk-sim : (i : Ix γ₁) → T γ₂
open Sim public

module _ {T : STX} where
  instance
    iLkSim : {{vrT : Vr T}} → Lk T (Sim T)
    lk {{iLkSim}} = lk-sim

    iWkSim : {{wkT : Wk T}} → {γ₁ : Dom} → Wk (Sim T γ₁)
    wk₁     {{iWkSim}}         (sim f) = sim (wk₁ ∘ f)
    wk      {{iWkSim}} δ       (sim f) = sim (wk δ ∘ f)
    wk-zero {{iWkSim {{wkT}}}} (sim f) = cong sim (ext (wk-zero {T} ∘ f))
      where postulate ext : Extensionality Level.zero Level.zero
    wk-suc {{iWkSim}} δ        (sim f) = cong sim (ext (wk-suc {T} δ ∘ f))
      where postulate ext : Extensionality Level.zero Level.zero

    iSnocSim : Snoc T (Sim T)
    snoc {{iSnocSim}} (sim f) t = sim λ
      { zero    → t
      ; (suc i) → f i
      }

    iUpSim : {{vrT : Vr T}} {{wkT : Wk T}} → Up (Sim T)
    _↑₁ {{iUpSim}} ξ = snoc {T} {Sim T} (wk₁ ξ) (vr {T} zero)
    _↑_ {{iUpSim}} ξ 0 = ξ
    _↑_ {{iUpSim}} ξ (suc δ⁺) = ξ ↑ δ⁺ ↑₁
    ↑-zero {{iUpSim}} ξ = refl
    ↑-suc {{iUpSim}} ξ δ⁺ = refl

    iIdmSim : {{vrT : Vr T}} → Idm (Sim T)
    idm {{iIdmSim}} γ = sim (vr {T})

    iWkmSim : {{vrT : Vr T}} → Wkm (Sim T)
    wkm {{iWkmSim}} δ = sim (vr {T} ∘ wk δ)

    iBetaSim : {{vrT : Vr T}} → Beta T (Sim T)
    beta {{iBetaSim}} t = snoc {T} {Sim T} (idm {Sim T} _) t

    iCompSim : {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} → Comp (Sim T)
    lk-sim (_⊙_ {{iCompSim}} ξ ζ) i =
      ap {T} {T} {Sim T} ζ (lk {T} {Sim T} ξ i)

    iLkUpSim : {{vrT : Vr T}} {{wkT : Wk T}} → LkUp T (Sim T)
    lk-↑₁-zero {{iLkUpSim}} ξ         = refl
    lk-↑₁-suc  {{iLkUpSim}} ξ zero    = refl
    lk-↑₁-suc  {{iLkUpSim}} ξ (suc i) = refl

    iLkWkmSim : {{vrT : Vr T}} → LkWkm T (Sim T)
    lk-wkm {{iLkWkmSim}} δ i = refl

    iLkIdmSim : {{vrT : Vr T}} → LkIdm T (Sim T)
    lk-idm {{iLkIdmSim}} i = refl

    iLkCompSim : {{vrT : Vr T}} {{wkT : Wk T}} {{apTT : Ap T T}} → LkCompAp T (Sim T)
    lk-⊙-ap {{iLkCompSim}} ξ₁ ξ₂ i = refl

--------------------------------------------------------------------------------

module SimIxInstances (T : STX) where

  instance
    iLkSimIx : {{vrT : Vr T}} → Lk T (Sim Ix)
    lk {{iLkSimIx}} ξ i = vr {T} (lk {Ix} {Sim Ix} ξ i)

    iLkUpSimIx : {{vrT : Vr T}} {{wkT : Wk T}}
      {{wkVrT : WkVr T}} → LkUp T (Sim Ix)
    lk-↑₁-zero {{iLkUpSimIx}} ξ   = refl
    lk-↑₁-suc  {{iLkUpSimIx}} ξ i = sym (wk₁-vr {T} (lk {Ix} {Sim Ix} ξ i))

    iLkWkmSimIx : {{vrT : Vr T}} → LkWkm T (Sim Ix)
    lk-wkm {{iLkWkmSimIx}} δ i = refl

    iLkIdmSimIx : {{vrT : Vr T}} → LkIdm T (Sim Ix)
    lk-idm {{iLkIdmSimIx}} i = refl

    iLkCompSimIx : {{vrT : Vr T}} {{apTT : Ap T T}}
      {{apVrT : ApVr T}} → LkCompAp T (Sim Ix)
    lk-⊙-ap {{iLkCompSimIx}} ξ₁ ξ₂ i =
      sym (ap-vr {T} {Sim Ix} ξ₂ (lk {Ix} {Sim Ix} ξ₁ i))

--------------------------------------------------------------------------------
