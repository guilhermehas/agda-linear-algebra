module Vector.Structures where

open import Level using (Level; _⊔_)
open import Function
open import Data.Nat
open import Data.Vec.Functional
open import Algebra
open import Algebra.BigOps

private variable
  a ℓ : Level
  n : ℕ

module VMonoid (rawMonoid : RawMonoid a ℓ) where

  open import Vector.Base public

  open RawMonoid rawMonoid renaming (Carrier to A)

  0ⱽ : Vector A n
  0ⱽ _ = ε

  _*ⱽ_ : Op₂ $ Vector A n
  (u *ⱽ v) i = u i ∙ v i

module VRing (rawRing : RawRing a ℓ) where

  open RawRing rawRing
  open VMonoid *-rawMonoid public
  open SumRawMonoid +-rawMonoid public
