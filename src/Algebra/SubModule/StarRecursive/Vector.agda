open import Level using (Level; _⊔_; zero)
open import Function
open import Algebra.SubModule.Base
open import Algebra.Bundles
open import Algebra.Module
open import Data.Nat as ℕ using (ℕ)
open import Data.List using (List)
open import Data.Vec.Functional
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous

import Algebra.SubModule.StarRecursive.Base as SubModuleBase
import Algebra.SubModule.StarRecursive.Properties as SubModuleProperties

module Algebra.SubModule.StarRecursive.Vector {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

open Ring ring
open LeftModule leftModule renaming (Carrierᴹ to A)
open SubModuleBase leftModule
open SubModuleProperties leftModule

private variable
  n : ℕ

_≈ⱽ_ : IRel (Vector A) _
xs ≈ⱽ ys = toList xs ≈ᴿ toList ys
