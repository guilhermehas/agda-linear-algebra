module Vec.Updates where

open import Level
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Functional using (Vector)
open import Relation.Binary.PropositionalEquality
open import Vec.Relation.FirstOrNot

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ
  b : Bool

evalFromListUpdates : (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) (i : Fin n)
  (firstOrNot : FirstOrNot (_≡ i) indices b) → A
evalFromListUpdates {b = false} xs values i firstOrNot = xs i
evalFromListUpdates {b = true} xs (x ∷ values) i (here _ _) = x
evalFromListUpdates {b = true} xs values i (there _ firstOrNot) = evalFromListUpdates xs (tail values) i firstOrNot
