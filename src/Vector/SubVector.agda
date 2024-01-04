module Vector.SubVector where

open import Level using (Level; levelOfType)
open import Function
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin
open import Data.Vec.Functional
open import Relation.Binary.PropositionalEquality

private variable
  a : Level
  A : Set a
  m n : ℕ

record SubVector (xs : Vector A n) (columns : Vector (Fin n) m) (ys : Vector A m) : Set (levelOfType A) where
  constructor subProp
  field
    subVecProp : ∀ i → ys i ≡ xs (columns i)
