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
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Vector.Structures
open import Algebra.BigOps
open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open Ring ring renaming (Carrier to A)
open LeftModule leftModule renaming (Carrierᴹ to M)
open import Algebra.Module.Instances.FunctionalVector ring using (is0) renaming (0ᴹ to 0V; _≈ᴹ_ to _≋_)
open SumMonoid +ᴹ-monoid

private variable
  ℓ : Level
  m n : ℕ
  zs : Vector M n

infix 4 _⊆ⱽ_ _⊇ⱽ_ _≋ⱽ_
infixr 7 _*ᵣ_

_*ᵣ_ : Vector A n → Op₁ $ Vector M n
(u *ᵣ v) i = u i *ₗ v i

_reaches_by_ : (xs : Vector M n) (x : M) (ys : Vector A n) → Set _
xs reaches x by ys = ∑ (ys *ᵣ xs) ≈ᴹ x

record _reaches_ (xs : Vector M n) (x : M) : Set (ℓm ⊔ rr) where
  constructor _by_
  field
    ys      : Vector A n
    xs*ys≈x : xs reaches x by ys

pattern vecGen ys = ys by _

span : Vector M n → Set _
span xs = ∃ (xs reaches_)

_⊆ⱽ_ _⊇ⱽ_ : (xs : Vector M m) (ys : Vector M n) → Set _
xs ⊆ⱽ ys = (xs reaches_) ⊆ (ys reaches_)
xs ⊇ⱽ ys = ys ⊆ⱽ xs

record _≋ⱽ_ (xs : Vector M m) (ys : Vector M n) : Set (ℓm ⊔ mr ⊔ rr) where
  field
    fwd : xs ⊆ⱽ ys
    bwd : ys ⊆ⱽ xs

_isSolutionOf_by_ : A → Vector M n → (M → Set ℓ) → Set _
α isSolutionOf v by ∑≡  = ∀ k → ∑≡ (α *ₗ v k)

IsLinearIndependent : Vector M n → Set _
IsLinearIndependent xs = ∀ {ys} (_ : ∑ (ys *ᵣ xs) ≈ᴹ 0ᴹ) → is0 ys

{-
Equivalent statements: (all about vectors in an m-dimensional space M)
  A: IsLinearIndependent {n} xs

  B: rank (makeMatrix {n} xs) ≡ n

  C: solve (makeSystem {n} xs) = { 0V }  -- informally

  D: case m of
         todo
       3 -> case n of
         0 -> True
         1 -> isNonZero xs
         2 -> not Collinear xs₁ xs₂
         3 -> cross (dot xs₁ xs₂) xs₃
         n -> False
       m -> fallback

Statements A, B, C should be equivalent (in LinAlg terms), and D is a
specialisation for a particular case (m=3).

-}
