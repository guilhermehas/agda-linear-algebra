open import Algebra.DecidableField

module MatrixFuncNormalization.MainTheo {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Algebra
open import Algebra.Apartness
open import Data.Product
open import Data.Nat.Base using (ℕ)

open import Algebra.Matrix.Structures

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)

open import MatrixFuncNormalization.NormAfter.PropsFlip dField
  hiding (module PNorm)
open import MatrixFuncNormalization.Definitions dField
open MRing rawRing hiding (matOps→func)

private variable
  m n : ℕ

mainTheo : (xs : Matrix F n m) → FromNormalization xs
mainTheo xs = let ys , pivs , mPivs , xs≈ⱽys , colsZero , pivsCrescent = allTheoremsTogether xs in record
  { ys = ys
  ; xs≈ⱽys = xs≈ⱽys
  ; ysNormed = record
    { pivs = pivs
    ; mPivots = mPivs
    ; pivsCrescent = pivsCrescent
    ; columnsZero = colsZero
    }
  }
