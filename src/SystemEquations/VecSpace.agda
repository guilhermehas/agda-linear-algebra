open import Algebra.Apartness

module SystemEquations.VecSpace {c ℓ₁ ℓ₂} (hField : HeytingField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Module
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

open import Vector.Structures
open import Algebra.Matrix.Structures
import Algebra.Module.Definition as MDefinition

open HeytingField hField renaming (Carrier to F)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing

open module MD {n} = MDefinition (leftModule n)

private variable
  m n : ℕ
