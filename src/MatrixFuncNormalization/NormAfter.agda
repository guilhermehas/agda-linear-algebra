open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.NormAfter {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import MatrixFuncNormalization.NormAfter.Base hField _≟_ public
open import MatrixFuncNormalization.NormAfter.Properties hField _≟_ public
