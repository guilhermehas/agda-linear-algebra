module Vec.Relation.FirstOrNot where

open import Level
open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Relation.Nullary

private variable
  ℓ : Level
  A : Set ℓ
  a : A
  b : Bool
  n : ℕ

data FirstOrNot (P : A → Set ℓ) : Vec A n → Bool → Set ℓ where
  notHere : FirstOrNot P [] false
  here    : (p : P a) (xs : Vec A n) → FirstOrNot P (a ∷ xs) true
  there   : (¬p : ¬ P a) {xs : Vec A n} (firstOrNot : FirstOrNot P xs b) → FirstOrNot P (a ∷ xs) b
