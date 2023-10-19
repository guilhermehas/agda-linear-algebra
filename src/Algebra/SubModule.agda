open import Algebra.Bundles
open import Algebra.Module

module Algebra.SubModule {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  where

open import Algebra.SubModule.Base leftModule public
open import Algebra.SubModule.Properties leftModule public
