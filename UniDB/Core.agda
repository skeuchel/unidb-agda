
module UniDB.Core where

open import Data.Nat public using (ℕ; suc; zero)
open import Data.Fin public using (Fin; suc; zero)
open import Function public using (id; _∘_)
open import Relation.Binary.PropositionalEquality as PropEq public
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)

open ≡-Reasoning public

Inj : {A B : Set} (f : A → B) → Set
Inj {A} f = {x y : A} → f x ≡ f y → x ≡ y

--------------------------------------------------------------------------------

Dom : Set
Dom = ℕ

infixl 10 _∪_
_∪_ : Dom → Dom → Dom
γ ∪ zero  = γ
γ ∪ suc δ = suc (γ ∪ δ)

∪-assoc : (γ₁ γ₂ γ₃ : Dom) → γ₁ ∪ (γ₂ ∪ γ₃) ≡ (γ₁ ∪ γ₂) ∪ γ₃
∪-assoc γ₁ γ₂ zero     = refl
∪-assoc γ₁ γ₂ (suc γ₃) = cong suc (∪-assoc γ₁ γ₂ γ₃)

--------------------------------------------------------------------------------

STX : Set₁
STX = Dom → Set

MOR : Set₁
MOR = Dom → Dom → Set

--------------------------------------------------------------------------------

Ix : STX
Ix = Fin
