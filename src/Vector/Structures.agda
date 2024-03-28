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
  infixl 7 _*ⱽ_

  open import Vector.Base public

  open RawMonoid rawMonoid renaming (Carrier to A)

  0ⱽ : Vector A n
  0ⱽ _ = ε

  _*ⱽ_ : Op₂ $ Vector A n
  (u *ⱽ v) i = u i ∙ v i

module VRing (rawRing : RawRing a ℓ) where
  infixl 7 _∙ⱽ_

  open RawRing rawRing renaming (Carrier to A)
  open VMonoid +-rawMonoid using (0ⱽ) public
  open VMonoid *-rawMonoid renaming (0ⱽ to 1ⱽ) public
  open SumRawMonoid +-rawMonoid public

  _∙ⱽ_ : (u v : Vector A n) → A
  u ∙ⱽ v = ∑ (u *ⱽ v )
