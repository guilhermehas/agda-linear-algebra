open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Base {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Function
open import Data.Product
open import Data.Maybe as Maybe
open import Data.Bool using (Bool; false; true; T)
open import Data.Nat using (ℕ)
open import Data.Vec.Functional as V
open import Relation.Nullary

open import Vector
open import Algebra.Matrix
open import Algebra.MatrixData renaming (Matrix to MatrixData)
open import MatrixFuncNormalization.NormAfter.Base dField

open DecidableField dField renaming (Carrier to F; heytingField to hField)

private variable
  m n : ℕ

is≠0 : F → Bool
is≠0 x = does $ x ≟ 0#

divideVec : Op₁ $ Vector F n
divideVec {n = n} xs = fromMaybe xs (Maybe.map (λ (_ , inv) i → inv * xs i) (findFirstWithProp xs fMaybe))
  where
  fMaybe : (x : F) → Maybe F
  fMaybe x = Maybe.map (proj₁ ∘ #⇒invertible) (decToMaybe $ x ≟ 0#)

divideByCoeff : Op₁ $ Matrix F n m
divideByCoeff = V.map divideVec

normalizeAndDivide : Op₁ $ Matrix F n m
normalizeAndDivide = divideByCoeff ∘ normalize

func⇒op₁⇒data : Op₁ $ Matrix F n m → Op₁ $ MatrixData F n m
func⇒op₁⇒data f = matrixFunc→Data ∘ f ∘ matrixData→Fun

normalizeData : Op₁ $ MatrixData F n m
normalizeData = func⇒op₁⇒data normalize

normalizeAndDivideData : Op₁ $ MatrixData F n m
normalizeAndDivideData = func⇒op₁⇒data normalizeAndDivide
