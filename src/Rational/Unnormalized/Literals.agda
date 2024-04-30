module Rational.Unnormalized.Literals where

import Data.Integer as ℤ
open import Data.Rational.Unnormalised

-2ℚᵘ -1ℚᵘ 2ℚᵘ 3ℚᵘ 5ℚᵘ : ℚᵘ
-2ℚᵘ = (ℤ.- (ℤ.+ 2)) / 1
-1ℚᵘ = (ℤ.- (ℤ.+ 1)) / 1
2ℚᵘ = ℤ.+ 2 / 1
3ℚᵘ = ℤ.+ 3 / 1
5ℚᵘ = ℤ.+ 5 / 1
