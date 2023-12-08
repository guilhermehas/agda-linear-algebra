module Rational.Unnormalized.Literals where

import Data.Integer as ℤ
open import Data.Rational.Unnormalised

-2ℚᵘ -1ℚᵘ 2ℚᵘ : ℚᵘ
-2ℚᵘ = (ℤ.- (ℤ.+ 2)) / 1
-1ℚᵘ = (ℤ.- (ℤ.+ 1)) / 1
2ℚᵘ = ℤ.+ 2 / 1
