module Algebra.Matrix.SubMatrix where

open import Level using (Level; levelOfType)
open import Function
open import Data.Product
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin
open import Data.Vec.Functional
open import Algebra.Matrix.Base
open import Relation.Binary.PropositionalEquality

private variable
  a : Level
  A : Set a
  m n p : ℕ

record SubMatrix (matrix : Matrix A n m) (columns : Vector (Fin m) p) : Set (levelOfType A) where
  field
    subMatrix : Matrix A n p
    subMatrixProp : ∀ i j → subMatrix i j ≡ matrix i (columns j)

SubMatrixΣ : Matrix A n m → Set _
SubMatrixΣ {m = m} xs = Σ ℕ (Vector (Fin m))
