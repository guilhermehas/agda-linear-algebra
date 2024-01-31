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
import MatrixFuncNormalization.NormAfter.AppendIdentity as AppendIdentity

open module F = NormAfter hField _≟_ using ()
  renaming (normalizeData to normalize;
            normalizeAndDivideData to normalizeAndDivide) public
module AI = AppendIdentity hField _≟_

private variable
  m n : ℕ

inverse : Matrix F n m → Matrix F n n
inverse = matrixFunc→Data ∘ AI.inverse ∘ matrixData→Fun
