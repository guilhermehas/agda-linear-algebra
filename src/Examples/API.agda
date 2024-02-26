module Examples.API where

open import Level
open import Algebra.Apartness
open import Data.Nat
open import Data.Vec
open import Relation.Binary
open import Algebra.DecidableField

open import Algebra.MatrixData
import MatrixDataNormalization.Base as Normed

private variable
  c ℓ ℓ₁ ℓ₂  : Level
  A : Set ℓ

module Examples (x y : A) where

  vec : Vec A 3
  vec = y ∷ x ∷ y ∷ []

  matrix : Matrix A 2 3
  matrix = (x ∷ y ∷ x ∷ []) ∷ vec ∷ []

module _ (dField : DecidableField c ℓ₁ ℓ₂)
  (open DecidableField dField)
  (x y : Carrier) where

  open DecidableField dField renaming (Carrier to F)
  open Examples x y
  open Normed dField

  normedMatrix : Matrix F 2 3
  normedMatrix = normalize matrix

  normedAndDividedMatrix : Matrix F 2 3
  normedAndDividedMatrix = normalizeAndDivide matrix

  inversedMatrix : Matrix F 2 2
  inversedMatrix = inverse matrix
