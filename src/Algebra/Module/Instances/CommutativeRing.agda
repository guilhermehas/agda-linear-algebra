open import Function using (_$_)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecSetoid
import Algebra.Definitions as AD
import Algebra.Structures as AS
open import Vector.Structures

module Algebra.Module.Instances.CommutativeRing
  {c ℓ} (cRing : CommutativeRing c ℓ) where

private variable
  n : ℕ

open CommutativeRing cRing
open import Algebra.Module.Instances.FunctionalVector ring
open import Algebra.Module.Instances.AllVecLeftModule ring
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open module AD′ {n} = AD (_≋_ {n})
open module AS′ {n} = AS (_≋_ {n})
open VRing rawRing renaming (0ⱽ to 𝟙)

*ⱽ-comm : Commutative {n} _*ⱽ_
*ⱽ-comm x y i = *-comm _ _

*ⱽ-isCommutativeRing : IsCommutativeRing {n} _+ᴹ_ _*ⱽ_ -ᴹ_ 𝟘 𝟙
*ⱽ-isCommutativeRing = record { isRing = v-isRing ; *-comm = *ⱽ-comm }

*ⱽ-commutativeRing : ℕ → CommutativeRing _ _
*ⱽ-commutativeRing n = record { isCommutativeRing = *ⱽ-isCommutativeRing {n}}
