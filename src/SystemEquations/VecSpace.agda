open import Algebra.Apartness

module SystemEquations.VecSpace {c ℓ₁ ℓ₂} (hField : HeytingField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Module
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

open import Vector.Structures
open import Algebra.Matrix.Structures

open HeytingField hField renaming (Carrier to F)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open VRing rawRing
open import Algebra.Module.Instances.FunctionalVector ring using (leftModule)
open MRing rawRing

import Algebra.Module.Definition as MDefinition
open module MD {n} = MDefinition (leftModule n) hiding (_isSolutionOf_)
open module LM {n} = LeftModule (leftModule n)

private variable
  m n : ℕ

_isSolutionOf_ : (x : Vector F m) (xs : Matrix F n m) → Set _
x isSolutionOf xs = ∀ i → x ∙ⱽ xs i ≈ 0#
