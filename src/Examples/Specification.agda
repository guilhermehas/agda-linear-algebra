{-# OPTIONS --allow-incomplete-matches #-}

module Examples.Specification where

open import Algebra
open import Algebra.DecidableField
open import Data.Product
open import Data.Rational
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Unit using (tt)
open import Rational.Literals
open import Rational.Properties
open import Algebra.Matrix.Structures
open import Vector.Structures

open DecidableField +-*-decidableField renaming (Carrier to F; heytingField to hField)

open MRing rawRing
open import SystemEquations.Definitions +-*-decidableField
open import SystemEquations.UniqueSolution +-*-decidableField
open VRing rawRing
open SystemEquations using (sol)

infix  4 _≋_
_≋_ = Pointwise _≈_

A : Matrix ℚ 2 2
A 0F 0F = 1
A 0F 1F = 1
A 1F 0F = 1
A 1F 1F = -1

b : Vector ℚ 2
b 0F = 3
b 1F = 1

LinEqProblem : Matrix ℚ 2 2 -> Vector ℚ 2 -> Set
LinEqProblem A b = Σ[ x ∈ Vector ℚ 2 ] (A *ᴹⱽ x ≋ b)

problem = Σ[ x ∈ Vector ℚ 2 ] (A *ᴹⱽ x ≋ b)
myLinEqProblem = LinEqProblem A b

sAb = system A b

open SystemEquations sAb using (Solution; IsSolution)

solAb : Solution
solAb = solveUniqueSystemEquations sAb

-- solX : problem
-- solX with sol _ x s ← solAb = x , s
