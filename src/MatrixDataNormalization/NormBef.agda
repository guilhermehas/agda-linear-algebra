open import Algebra.Apartness
open import Relation.Binary

module MatrixDataNormalization.NormBef {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Algebra
open import Function
open import Data.Product
open import Data.List
open import Data.Nat using (ℕ)
open import Data.Rational.Unnormalised hiding (truncate)
open import Data.Rational.Unnormalised.Properties
import MatrixFuncNormalization.normBef as NormField

open import Algebra.MatrixData
import Algebra.Module.VecSpace as VecSpace
open import Rational.Properties

open NormField hField _≟_ hiding (getCoeff)
open PVec


private variable
  m n : ℕ

normalizeBef : Op₁ $ Matrix F n m
normalizeBef = matrixFunc→Data ∘ proj₁ ∘ proj₁ ∘ normalizeMatrix ∘ matrixData→Fun

getCoeff : Matrix F n m → List _
getCoeff xs = let
  xsFunc = matrixData→Fun xs
  res@(_ , _ , xs≈ⱽys) = normalizeMatrix xsFunc
  in ≈ⱽ⇒listVops xs≈ⱽys
