module Algebra.BigOpsData where

open import Level using (Level)
open import Function
open import Algebra
open import Data.Product
import Data.Sum as Sum
open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Fin as F using (Fin; _≟_; zero; suc; punchIn)
open import Data.Fin.Properties
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong)
open import Relation.Nullary.Decidable
open import Vector.Properties
open import Relation.Binary
open import Relation.Nullary

open import Algebra.Ring.Properties
open import Vector

private variable
  a ℓ : Level
  m n : ℕ

module SumRawMonoid (rawMonoid : RawMonoid a ℓ) where

  open RawMonoid rawMonoid renaming (Carrier to A)

  private variable
    V W : Vec A n

  ∑ : Vec A n → A
  ∑ = foldr _ _∙_ ε

module SumRawRing (rawRing : RawRing a ℓ) where

  open RawRing rawRing renaming (Carrier to A)
  open SumRawMonoid +-rawMonoid public

  δ : (i j : Fin n) → A
  δ i j with i ≟ j
  ... | true  because _ = 1#
  ... | false because _ = 0#

  δii≡1# : ∀ i → δ {n} i i ≡ 1#
  δii≡1# i rewrite dec-yes (i F.≟ i) ≡.refl .proj₂ = ≡.refl

  δss≡δ : (i j : Fin n) → δ (suc i) (suc j) ≡ δ i j
  δss≡δ i j with i ≟ j
  ... | true  because _ = ≡.refl
  ... | false because _ = ≡.refl

module SumMonoid (monoid : Monoid a ℓ) where

  open Monoid monoid renaming (Carrier to A)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open SumRawMonoid rawMonoid public

module SumCommMonoid (cMonoid : CommutativeMonoid a ℓ) where

  open CommutativeMonoid cMonoid renaming (Carrier to A)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open SumMonoid monoid public
  open import Algebra.Solver.CommutativeMonoid cMonoid using (solve; _⊜_; _⊕_)

module SumRing (ring : Ring a ℓ) where

  open Ring ring renaming (Carrier to A)
  open SumRawRing rawRing using (∑; δ; δss≡δ; δii≡1#) public
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open Units ring
  open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid using (solve; _⊜_; _⊕_)
