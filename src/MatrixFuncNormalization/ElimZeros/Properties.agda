open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Properties {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Function
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
open import MatrixFuncNormalization.normBef dField using (VecPivotPos; MatrixPivots)
open import MatrixFuncNormalization.ElimZeros.Base dField hiding (divideVec)
open import MatrixFuncNormalization.NormAfter.Properties dField using (ColumnsZero; Maybe≈0)
open import MatrixFuncNormalization.NormAfter.PropsFlip dField
open import MatrixFuncNormalization.Definitions dField

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (ring)
open import Algebra.HeytingField.Properties hField
open import Algebra.Ring.Properties

open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid
open Units ring

private variable
  m n : ℕ

divideVec : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec xs ⊤⁺ vPos i = xs i
divideVec xs [ p ] (xp#0 , _) i = #⇒invertible xp#0 .proj₁ * xs i

divideVecPreservesPos : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → VecPivotPos (divideVec xs p vPos) p
divideVecPreservesPos xs ⊤⁺ vPos = vPos
proj₁ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) = x#0y#0→xy#0 (x⁻¹#0 _ _) xp#0
proj₂ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) i i<p = begin
  _ * xs i ≈⟨ *-congˡ (xi≈0 i i<p) ⟩
  _ * 0#   ≈⟨ zeroʳ _ ⟩
  0# ∎

divideVec≈0 : ∀ {xs : Vector F n} {q} (vPos : VecPivotPos xs q) p → xs p ≈ 0# → divideVec xs q vPos p ≈ 0#
divideVec≈0 {q = [ q ]} vPos p xsP≈0 = trans (*-congˡ xsP≈0) (0RightAnnihilates _)
divideVec≈0 {q = ⊤⁺} vPos p = id


module _ (xs : Matrix F n m) (xsNormed : FromNormalization xs) where

  open FromNormalization xsNormed

  matDivided : Matrix F n m
  matDivided i = divideVec (ys i) (pivs i) (mPivots i)

  mPivAfter : MatrixPivots matDivided pivs
  mPivAfter _ = divideVecPreservesPos _ _ _

  columnsZeros : ColumnsZero matDivided pivs
  columnsZeros i j i≢j = helper (columnsZero i j i≢j)
    where
    helper : Maybe≈0 (ys j) (pivs i) → Maybe≈0 (divideVec (ys j) (pivs j) (mPivots j)) (pivs i)
    helper with pivs i
    ... | ⊤⁺  = λ _ → _
    ... | [ p ]  = divideVec≈0 (mPivots j) p
