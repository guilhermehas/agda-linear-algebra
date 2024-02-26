open import Algebra.Apartness
open import Relation.Binary
open import Algebra.DecidableField

module MatrixDataNormalization.Base {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Function
open import Data.Nat using (ℕ)

open import Algebra.MatrixData
import MatrixFuncNormalization.NormAfter.Base as NormAfter
import MatrixFuncNormalization.NormAfter.AppendIdentity as AppendIdentity

open DecidableField dField renaming (Carrier to F)
open module F = NormAfter dField using ()
  renaming (normalizeData to normalize;
            normalizeAndDivideData to normalizeAndDivide) public
module AI = AppendIdentity dField

private variable
  m n : ℕ

inverse : Matrix F n m → Matrix F n n
inverse = matrixFunc→Data ∘ AI.inverse ∘ matrixData→Fun
