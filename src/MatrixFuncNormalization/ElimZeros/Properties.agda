open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Properties {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level using (Level)
open import Algebra
open import Algebra.Apartness
open import Function
open import Data.Product
open import Data.Fin as F using (Fin; zero; suc; inject!; toℕ)
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.Maybe
open import Data.Sum
-- open import Data.Bool using (Bool; false; true; T)
open import Data.Nat using (ℕ; NonZero; z≤n; s<s)
open import Data.Vec.Functional as V
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
-- open import Relation.Nullary
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong)
open import Relation.Binary.Construct.Add.Supremum.Strict

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
open PNorm

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

mPivs≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs)
  → MatrixPivots≁0 (xs ∘ inject!) (normPivs pivs)
mPivs≁0′ {n = ℕ.suc n} xs pivs mPivs i with pivs 0F | mPivs 0F
mPivs≁0′ {_} {ℕ.suc n} xs pivs mPivs 0F | just x | c  = c
mPivs≁0′ {_} {ℕ.suc n} xs pivs mPivs (suc i) | just x | _ = mPivs≁0′ (tail xs) (tail pivs) (mPivs ∘ suc) i

normPivsSame : ∀ (pivs : Vector (Fin m ⁺) n) i → just (normPivs pivs i) ≡ pivs (inject! i)
normPivsSame {n = ℕ.suc n} pivs i with pivs 0F in eq
normPivsSame {n = ℕ.suc n} pivs 0F | just x rewrite eq = ≡.refl
normPivsSame {n = ℕ.suc n} pivs (suc i) | just x rewrite eq = normPivsSame {n = n} (tail pivs) i

private
  injectPreserves : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → i F.< j → inject! i F.< inject! j
  injectPreserves {ℕ.suc n} {k = suc k} {0F} {suc j} (s<s z≤n) = s<s z≤n
  injectPreserves {ℕ.suc n} {k = suc k} {suc i} {suc j} (s<s i<j) = s<s (injectPreserves i<j)

  inject⇒≡ : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → inject! i ≡ inject! j → i ≡ j
  inject⇒≡ {ℕ.zero} {0F} {i = ()} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = 0F} {0F} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = 0F} {suc j} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = suc i} x
  inject⇒≡ {ℕ.suc n} {suc k} {0F} {0F} ≡.refl = ≡.refl
  inject⇒≡ {ℕ.suc n} {suc k} {suc i} {suc j} eq rewrite inject⇒≡ (suc-injective eq) = ≡.refl

  inject⇒≢ : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → i ≢ j → inject! i ≢ inject! j
  inject⇒≢ = _∘ inject⇒≡

pivsCrescent≁0′ : {pivs : Vector (Fin m ⁺) n} (normed : AllRowsNormalized pivs) → AllRowsNormalized≁0 (normPivs pivs)
pivsCrescent≁0′ {pivs = pivs} normed {i} {j} i<j = helper $ normed _ _ $ injectPreserves i<j
  where
  helper2 : _ → _
  helper2 (inj₁ [ pI<pJ ]) = pI<pJ

  helper : pivs (inject! i) <′ pivs (inject! j) → _
  helper rewrite ≡.sym (normPivsSame pivs i) | ≡.sym (normPivsSame pivs j) = helper2

cols0≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (cols0 : ColumnsZero xs pivs)
  → ColumnsZero≁0 (xs ∘ inject!) (normPivs pivs)
cols0≁0′ {n = ℕ.suc n} xs pivs cols0 i j i≢j = helper $ cols0 _ _ $ inject⇒≢ i≢j
  where
  helper : Maybe≈0 (xs (inject! j)) (pivs (inject! i)) → _
  helper rewrite ≡.sym (normPivsSame pivs i) = id

pivsOne≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (pivsOne : PivsOne xs pivs)
  → PivsOne≁0 (xs ∘ inject!) (normPivs pivs)
pivsOne≁0′ {n = ℕ.suc n} xs pivs pivsOne i with pivs 0F | pivsOne 0F
pivsOne≁0′ {_} {ℕ.suc n} xs pivs pivsOne 0F | just a | just b = b
pivsOne≁0′ {_} {ℕ.suc n} xs pivs pivsOne (suc i) | just a | just b = pivsOne≁0′ (tail xs) (tail pivs) (pivsOne ∘ F.suc) i

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

  ys≁0 : Matrix F n′ m
  ys≁0 = ys ∘ inject! {i = sizeF}
  pivs≁0 = normPivs pivs

  mPivs≁0 : MatrixPivots≁0 ys≁0 pivs≁0
  mPivs≁0 = mPivs≁0′ ys pivs mPivots

  pivsCrescent≁0 : AllRowsNormalized≁0 pivs≁0
  pivsCrescent≁0 x<y = pivsCrescent≁0′ pivsCrescent x<y

  colsZero : ColumnsZero≁0 ys≁0 pivs≁0
  colsZero = cols0≁0′ _ _ columnsZero

  pivsOne≁0 : PivsOne ys pivs → PivsOne≁0 ys≁0 pivs≁0
  pivsOne≁0 = pivsOne≁0′ _ _
