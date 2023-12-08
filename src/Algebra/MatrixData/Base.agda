module Algebra.MatrixData.Base where

open import Level using (Level)
open import Function
open import Data.Nat as ℕ using (ℕ)
open import Data.Vec

import Data.Vec.Functional as F

import Algebra.Matrix as F

private variable
  a : Level
  A : Set a
  m n p : ℕ

Matrix : Set a → (n m : ℕ) → Set a
Matrix A n m = Vec (Vec A m) n

matrixFunc→Data : F.Matrix A n m → Matrix A n m
matrixFunc→Data = tabulate ∘ (tabulate ∘_)

matrixData→Fun : Matrix A n m → F.Matrix A n m
matrixData→Fun = (lookup ∘_) ∘ lookup
