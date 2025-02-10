{-# OPTIONS --allow-incomplete-matches #-}

module Examples.Specification where

open import Algebra
open import Algebra.DecidableField
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
open SystemEquations sAb using (Solution)

solAb : Solution
solAb = solveUniqueSystemEquations sAb

x : Vector ℚ 2
x with sol _ aff _ ← solAb = aff

spec : ∀ r → A r ∙ⱽ x ≈ b r
spec with sol _ _ s ← solAb = s
