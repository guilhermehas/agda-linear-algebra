module Examples.API where

open import Level
open import Algebra.Apartness
open import Data.Nat
open import Data.Vec
open import Relation.Binary

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

module _ (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField)
  (_≟_ : Decidable _#_) (x y : Carrier) where

  open HeytingField hField renaming (Carrier to F)
  open Examples x y
  open Normed hField _≟_

  normedMatrix : Matrix F 2 3
  normedMatrix = normalize matrix

  inversedMatrix : Matrix F 2 2
  inversedMatrix = inverse matrix
