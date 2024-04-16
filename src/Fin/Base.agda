module Fin.Base where

open import Function
open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ)

private variable
  n : ℕ

predFin : Fin (ℕ.suc $ ℕ.suc n) → Fin $ ℕ.suc n
predFin 0F = 0F
predFin (suc i) = i
