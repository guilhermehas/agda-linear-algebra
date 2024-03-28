open import Algebra
open import Algebra.Module

module Algebra.Module.Definition {rr ℓr mr ℓm}
  {ring : Ring rr ℓr}
  (leftModule : LeftModule ring mr ℓm)
  where

open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary
open import Relation.Unary
open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Vector.Structures
open import Algebra.BigOps
open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open Ring ring renaming (Carrier to A)
open LeftModule leftModule renaming (Carrierᴹ to M)
open SumMonoid +ᴹ-monoid

private variable
  ℓ : Level
  m n : ℕ

infix 4 _⊆ⱽ_ _⊇ⱽ_ _≋ⱽ_
infixr 7 _*ᵣ_

_*ᵣ_ : Vector A n → Op₁ $ Vector M n
(u *ᵣ v) i = u i *ₗ v i

record _reaches_ (xs : Vector M n) (x : M) : Set (ℓm ⊔ rr) where
  constructor _by_
  field
    ys      : Vector A n
    xs*ys≈x : ∑ (ys *ᵣ xs) ≈ᴹ x

_⊆ⱽ_ _⊇ⱽ_ : (xs : Vector M m) (ys : Vector M n) → Set _
xs ⊆ⱽ ys = (xs reaches_) ⊆ (ys reaches_)
xs ⊇ⱽ ys = ys ⊆ⱽ xs

record _≋ⱽ_ (xs : Vector M m) (ys : Vector M n) : Set (ℓm ⊔ mr ⊔ rr) where
  field
    fwd : xs ⊆ⱽ ys
    bwd : ys ⊆ⱽ xs

_isSolutionOf_by_ : A → Vector M n → (M → Set ℓ) → Set _
α isSolutionOf v by ∑≡  = ∀ k → ∑≡ (α *ₗ v k)
