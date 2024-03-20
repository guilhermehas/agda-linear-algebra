open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Properties {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Function
open import Data.Product
open import Data.Fin as F using (Fin; zero; suc; inject!; toℕ)
open import Data.Fin.Patterns
open import Data.Maybe
-- open import Data.Bool using (Bool; false; true; T)
open import Data.Nat using (ℕ; NonZero)
open import Data.Vec.Functional as V
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
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
import Algebra.Module.Definition as MDefinition
import Algebra.Module.PropsField as PField
open import Algebra.Module.Instances.FunctionalVector ring

open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid
open Units ring
open module PFieldN {n} = PField heytingCommutativeRing (leftModule n)
open module MDefN {n} = MDefinition (leftModule n)


private variable
  m n : ℕ

invVecValue : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → F
invVecValue xs ⊤⁺ vPos = 1#
invVecValue xs [ p ] (xp#0 , _) = proj₁ (#0⇒invertible xp#0)

divideVec : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec xs ⊤⁺ vPos i = xs i
divideVec xs [ p ] (xp#0 , _) i = #⇒invertible xp#0 .proj₁ * xs i

divideVec₂ : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec₂ xs p vPos i = invVecValue xs p vPos * xs i

dV₂≈dV : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → divideVec₂ xs p vPos ≋ divideVec xs p vPos
dV₂≈dV xs ⊤⁺ vPos _ = *-identityˡ _
dV₂≈dV xs [ p ] vPos i = refl

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

divideVecP≈1 : ∀ {xs : Vector F n} {p} (vPos : VecPivotPos xs p) → All (λ i → divideVec xs p vPos i ≈ 1#) p
divideVecP≈1 {xs = xs} {[ i ]} (xsI#0 , _) = let x⁻¹ = #⇒invertible xsI#0 .proj₁ in just (begin
  x⁻¹ * xs i       ≈˘⟨ *-congˡ (trans (+-congˡ -0#≈0#) (+-identityʳ _)) ⟩
  x⁻¹ * (xs i - 0#) ≈⟨ #⇒invertible xsI#0 .proj₂ .proj₁ ⟩
  1# ∎)
divideVecP≈1 {p = ⊤⁺} vPos = nothing

invVecValue#0 : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → invVecValue xs p vPos # 0#
invVecValue#0 xs ⊤⁺ vPos = 1#0
invVecValue#0 xs [ p ] vPos = x⁻¹#0 _ _

firstZero : Vector (Fin m ⁺) n → Fin (ℕ.suc n)
firstZero {n = ℕ.zero} xs = 0F
firstZero {n = ℕ.suc n} xs = maybe′ (const (suc (firstZero (tail xs)))) 0F (xs 0F)

normPivs : ∀ (pivs : Vector (Fin m ⁺) n) → Vector (Fin m) (toℕ (firstZero pivs))
normPivs {n = ℕ.suc n} pivs i with pivs 0F
normPivs {n = ℕ.suc n} pivs 0F | just i = i
normPivs {n = ℕ.suc n} pivs (suc i) | just _ = normPivs (tail pivs) i

module _ {xs : Matrix F n m} (xsNormed : FromNormalization xs) where

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

  pivsOne : PivsOne matDivided pivs
  pivsOne _ = divideVecP≈1 _

  ys≋ⱽmNormed : ys ≋ⱽ matDivided
  ys≋ⱽmNormed = ≋ⱽ-trans (*#0≈ⱽ ys λ i → invVecValue#0 (ys i) (pivs i) (mPivots i))
    (≋⇒≋ⱽ λ i → dV₂≈dV (ys i) (pivs i) (mPivots i))

  xs≋ⱽmNormed : xs ≋ⱽ matDivided
  xs≋ⱽmNormed = ≋ⱽ-trans xs≋ⱽys ys≋ⱽmNormed

  normalizeOne : FromNormalization≈1 xs
  normalizeOne = record
    { ysNormed = record
      { isNormed = record
        { mPivots      = mPivAfter
        ; pivsCrescent = pivsCrescent
        ; columnsZero  = columnsZeros
        }
      ; pivsOne  = pivsOne
      }
    ; xs≋ⱽys   = xs≋ⱽmNormed
    }

  -- Removing Zeros

  sizeF = firstZero pivs
  n′ = toℕ sizeF
  nPivs = normPivs pivs
