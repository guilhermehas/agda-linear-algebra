open import Algebra.DecidableField

module SystemEquations.VecBool {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Vec.VecBool.Base

open DecidableField dField renaming (Carrier to F) hiding (sym)
