open import Algebra.Apartness
open import Relation.Binary
open import Algebra.DecidableField

module MatrixDataNormalization.NormBef {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

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
open import Rational.Unnormalized.Properties

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open NormField dField hiding (getCoeff)
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
