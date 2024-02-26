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
  open import Algebra.BigOps

  open Ring ring renaming (Carrier to A)
  open LeftModule leftModule renaming (Carrierᴹ to M)


  private variable
    n : ℕ

  record _reaches_ (xs : Vector M n) (x : M) : Set (ℓm ⊔ rr) where
    field
      ys      : Vector A n
      xs*ys≈x : foldr _+ᴹ_ 0ᴹ (λ i → ys i *ₗ xs i) ≈ᴹ x

  _⊆ⱽ_ : (xs ys : Vector M n) → Set _
  xs ⊆ⱽ ys = (xs reaches_) ⊆ (ys reaches_)

  record _≋ⱽ_ (xs ys : Vector M n) : Set (ℓm ⊔ mr ⊔ rr) where
    field
      fwd : xs ⊆ⱽ ys
      bwd : ys ⊆ⱽ xs
