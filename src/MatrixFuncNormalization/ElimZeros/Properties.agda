open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Properties {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

-- open import Algebra
open import Algebra.Apartness
-- open import Function
open import Data.Product
open import Data.Fin as F using (Fin; zero; suc)
-- open import Data.Maybe as Maybe
-- open import Data.Bool using (Bool; false; true; T)
open import Data.Nat using (ℕ)
open import Data.Vec.Functional as V
-- open import Relation.Nullary
open import Relation.Nullary.Construct.Add.Supremum

-- open import Vector
open import Algebra.Matrix
-- open import Algebra.MatrixData renaming (Matrix to MatrixData)
-- open import MatrixFuncNormalization.normBef dField using (findNonZeroPos)
-- open import MatrixFuncNormalization.NormAfter.Base dField
open import MatrixFuncNormalization.normBef dField using (VecPivotPos; MatrixPivots)
open import MatrixFuncNormalization.ElimZeros.Base dField hiding (divideVec)
open import MatrixFuncNormalization.NormAfter.PropsFlip dField

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)

open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid

private variable
  m n : ℕ

divideVec : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec xs ⊤⁺ vPos i = xs i
divideVec xs [ p ] (xp#0 , _) i = #⇒invertible xp#0 .proj₁ * xs i

divideVecPreservesPos : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → VecPivotPos (divideVec xs p vPos) p
divideVecPreservesPos xs ⊤⁺ vPos = vPos
proj₁ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) = x#0y#0→xy#0 {!!} xp#0
proj₂ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) i i<p = begin
  _ * xs i ≈⟨ *-congˡ (xi≈0 i i<p) ⟩
  _ * 0#   ≈⟨ zeroʳ _ ⟩
  0# ∎

module _ (xs : Matrix F n m) where

  matAfterNorm = allTheoremsTogether xs
  ys = matAfterNorm .proj₁
  pivs = matAfterNorm .proj₂ .proj₁
  mPivs = matAfterNorm .proj₂ .proj₂ .proj₁

  matDivided : Matrix F n m
  matDivided i = divideVec (ys i) (pivs i) (mPivs i)

  mPivAfter : MatrixPivots matDivided pivs
  mPivAfter _ = divideVecPreservesPos _ _ _
