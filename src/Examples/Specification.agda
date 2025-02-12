{-# OPTIONS --allow-incomplete-matches #-}

module Examples.Specification where

open import Algebra
open import Algebra.DecidableField
open import Data.Product
open import Data.Rational
open import Data.Vec.Functional
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

A : Matrix ℚ 2 2
A 0F 0F = 1
A 0F 1F = 1
A 1F 0F = 1
A 1F 1F = -1

b : Vector ℚ 2
b 0F = 3
b 1F = 1

sAb = system A b
problem = Σ[ x ∈ Vector ℚ 2 ] (∀ r → A r ∙ⱽ x ≈ b r)
open SystemEquations sAb using (Solution; IsSolution)

solAb : Solution
solAb = solveUniqueSystemEquations sAb

solX : problem
solX with sol _ x s ← solAb = x , s
