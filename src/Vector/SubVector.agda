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

-- This is a 3-arg. predicate, but the "corresponding" SubMatrix is a 2-arg. "container" of a matrix.
record SubVector (xs : Vector A n) (columns : Vector (Fin n) m) (ys : Vector A m) : Set (levelOfType A) where
  constructor subProp
  field
    subVecProp : ∀ i → ys i ≡ xs (columns i)

-- Another way could be to have SubVector xs ys where field columns : ...
