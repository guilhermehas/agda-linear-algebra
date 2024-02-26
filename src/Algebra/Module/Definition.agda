open import Algebra
open import Algebra.Module

module Algebra.Module.Definition {rr ℓr mr ℓm}
  {ring : Ring rr ℓr}
  (leftModule : LeftModule ring mr ℓm)
  where

  open import Level using (Level; _⊔_)
  open import Relation.Binary
  open import Relation.Unary
  open import Data.Nat using (ℕ)
  open import Data.Vec.Functional
  open import Vector.Structures

  open Ring ring renaming (Carrier to A)
  open VRing rawRing

  private variable
    n : ℕ

  record _reaches_ (xs : Vector A n) (x : A) : Set (ℓr ⊔ rr) where
    field
      ys      : Vector A n
      xs*ys≈x : ∑ (ys *ⱽ xs) ≈ x

  _⊆ⱽ_ : (xs ys : Vector A n) → Set _
  xs ⊆ⱽ ys = (xs reaches_) ⊆ (ys reaches_)

  record _≋ⱽ_ (xs ys : Vector A n) : Set (ℓr ⊔ rr) where
    field
      fwd : xs ⊆ⱽ ys
      bwd : ys ⊆ⱽ xs
