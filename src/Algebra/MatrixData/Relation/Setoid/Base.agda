open import Relation.Binary

module Algebra.MatrixData.Relation.Setoid.Base
  {a ℓ} (S : Setoid a ℓ) where

open import Data.Nat using (ℕ)
open import Algebra.MatrixData
import Data.Vec.Relation.Binary.Equality.Setoid as VSetoid
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise

open Setoid S renaming (Carrier to A)

module ≈ = VSetoid S
module ≋ {n} = VSetoid (≈.≋-setoid n)

private variable
  m n : ℕ


_≋_ : ∀ {m n} → REL (Matrix A n m) (Matrix A n m) _
_≋_ = ≋._≋_

≋-setoid : ℕ → ℕ → Setoid _ _
≋-setoid n m = ≋.≋-setoid {n} m

decidable : Decidable _≈_ → Decidable (_≋_ {n} {m})
decidable dec = Pointwise.decidable (Pointwise.decidable dec)
