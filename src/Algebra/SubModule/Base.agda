open import Level
open import Function
open import Data.Product
open import Relation.Unary
open import Algebra.Bundles
open import Algebra.Module

module Algebra.SubModule.Base {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  where

open Ring ring
open LeftModule leftModule
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
open import Algebra.Solver.CommutativeMonoid +ᴹ-commutativeMonoid
open import Algebra.Definitions (_≐_ {_} {Carrierᴹ} {ℓm})

private variable
  ℓ ℓ′ : Level

Cᴹ : (ℓ : Level) → Set (ℓm ⊔ suc ℓ)
Cᴹ ℓ = Pred Carrierᴹ ℓ

0ₛ : Cᴹ ℓm
0ₛ = _≈ᴹ 0ᴹ

_+ₛ_ : Cᴹ ℓm → Cᴹ ℓm → Cᴹ ℓm
(xs +ₛ ys) z = ∃⟨ (λ ((x , y) : Carrierᴹ × Carrierᴹ) → x ∈ xs × y ∈ ys × x +ᴹ y ≈ᴹ z) ⟩

span : Carrierᴹ → Cᴹ ℓm
span v x = ∃⟨ (λ r → r *ₗ v ≈ᴹ x) ⟩
