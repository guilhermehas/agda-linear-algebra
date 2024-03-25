open import Algebra.DecidableField

module MatrixFuncNormalization.MainTheo {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
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
open import MatrixFuncNormalization.ElimZeros.Properties dField
open import Algebra.Module.Instances.FunctionalVector ring
import Algebra.Module.Props as MProps
open module P′ {n} = MProps commutativeRing (leftModule n)

private variable
  m n : ℕ

normalize : (xs : Matrix F n m) → FromNormalization xs
normalize xs = let ys , pivs , mPivs , xs≈ⱽys , colsZero , pivsCrescent = allTheoremsTogether xs in record
  { xs≈ⱽys   = xs≈ⱽys
  ; ysNormed = record
    { mPivots      = mPivs
    ; pivsCrescent = pivsCrescent
    ; columnsZero  = colsZero
    }
  }

normalize≈1 : (xs : Matrix F n m) → FromNormalization≈1 xs
normalize≈1 xs = record { ysNormed = ysIsNormed≈1 ; xs≋ⱽys = ≋ⱽ-trans xs≋ⱽys xs≋ⱽys₂ }
  where
  open FromNormalization (normalize xs)
  open FromNormed (record { isNormed = ysNormed }) renaming (xs≋ⱽys to xs≋ⱽys₂)

normalize≈1≁0 : (xs : Matrix F n m) → FromNormalization≁0≈1 xs _
normalize≈1≁0 xs = record { ysNormed = xs≁0Normed ; xs≋ⱽys = ≋ⱽ-trans xs≋ⱽys xs≋ⱽxs≁0 }
  where
  open FromNormalization≈1 (normalize≈1 xs)
  open FromNormed≈1 (record { isNormed≈1 = ysNormed }) hiding (xs≋ⱽys)
