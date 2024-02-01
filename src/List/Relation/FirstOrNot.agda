module List.Relation.FirstOrNot where

open import Level
open import Data.Bool
open import Data.List
open import Relation.Nullary

private variable
  ℓ : Level
  A : Set ℓ
  a : A
  b : Bool

data FirstOrNot (P : A → Set ℓ) : List A → Bool → Set ℓ where
  notHere : FirstOrNot P [] false
  here    : (p : P a) (xs : List A) → FirstOrNot P (a ∷ xs) true
  there   : (¬p : ¬ P a) {xs : List A} (firstOrNot : FirstOrNot P xs b) → FirstOrNot P (a ∷ xs) b
