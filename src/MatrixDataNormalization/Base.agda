open import Algebra.Apartness
open import Relation.Binary

module MatrixDataNormalization.Base {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Algebra
open import Function
open import Data.Nat using (ℕ)

open import Algebra.MatrixData
import MatrixFuncNormalization.NormAfter.Base as NormAfter

module F = NormAfter hField _≟_

private variable
  m n : ℕ

normalize : Op₁ $ Matrix F n m
normalize = matrixFunc→Data ∘ F.normalize ∘ matrixData→Fun
