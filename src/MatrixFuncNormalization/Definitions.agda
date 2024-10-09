open import Algebra.DecidableField

module MatrixFuncNormalization.Definitions {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
open import Algebra
open import Algebra.Apartness
open import Data.Bool.Base hiding (_<_)
open import Data.List as L using (List)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All
open import Data.Product
open import Data.Nat.Base using (ℕ)
open import Data.Fin as F using (Fin; _<_)
open import Data.Vec.Functional
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps

open import Algebra.Matrix.Structures

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing

open import MatrixFuncNormalization.normBef dField
open import MatrixFuncNormalization.NormAfter.PropsFlip dField
  hiding (module PNorm)
open import MatrixFuncNormalization.NormAfter.Properties dField
  using (ColumnsZero)
open import Algebra.Module.Base ring
open MRing rawRing hiding (matOps→func)
open module MDef {n} = MDefinition (M.leftModule n)
open module MProp {n} = MProps commutativeRing (M.leftModule n)

open PVec
open PNorm

private variable
  m n p : ℕ
  α : F

record MatrixIsNormed (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    pivs         : Vector (Fin m ⁺) n
    mPivots      : MatrixPivots xs pivs
    pivsCrescent : AllRowsNormalized pivs
    columnsZero  : ColumnsZero xs pivs

record MatrixNormed (m n : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    xs       : Matrix F n m
    isNormed : MatrixIsNormed xs

  open MatrixIsNormed isNormed public

PivsOne : ∀ (xs : Matrix F n m) (pivs : Vector (Fin m ⁺) n) → Set _
PivsOne xs pivs = ∀ i → All (λ j → xs i j ≈ 1#) (pivs i)

record MatrixIsNormed≈1 (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    isNormed : MatrixIsNormed xs

  open MatrixIsNormed isNormed public

  field
    pivsOne  : PivsOne xs pivs


record MatrixNormed≈1 (m n : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    xs         : Matrix F n m
    isNormed≈1 : MatrixIsNormed≈1 xs

  open MatrixIsNormed≈1 isNormed≈1 public

  xsNormed : MatrixNormed m n
  xsNormed = record { isNormed = isNormed }


record FromNormalization′ (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ys       : Matrix F n m
    ysNormed : MatrixIsNormed ys
    xs≋ⱽys   : xs ≋ⱽ ys

  open MatrixIsNormed ysNormed public

record FromNormalization (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ys       : Matrix F n m
    ysNormed : MatrixIsNormed ys
    xs≈ⱽys   : xs ≈ⱽ ys

  open MatrixIsNormed ysNormed public

  listOps : List $ VecOp n
  listOps = ≈ⱽ⇒listVops xs≈ⱽys

  reproduceOperations : Op₁ $ Matrix F n p
  reproduceOperations xs = L.foldr matOps→func xs listOps

  inverseMatrix : Matrix F n n
  inverseMatrix = reproduceOperations 1ᴹ

  xs≋ⱽys : xs ≋ⱽ ys
  xs≋ⱽys = ≈ⱽ⇒≋ⱽ xs≈ⱽys

  fromNormalization′ : FromNormalization′ xs
  fromNormalization′ = record
    { ysNormed = ysNormed
    ; xs≋ⱽys   = xs≋ⱽys
    }

record FromNormalization≈1 (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ys       : Matrix F n m
    ysNormed : MatrixIsNormed≈1 ys
    xs≋ⱽys   : xs ≋ⱽ ys

  open MatrixIsNormed≈1 ysNormed public

  fromNormalization : FromNormalization′ xs
  fromNormalization = record
    { ysNormed = record
      { mPivots = mPivots
      ; pivsCrescent = pivsCrescent
      ; columnsZero = columnsZero
      }
    ; xs≋ⱽys = xs≋ⱽys
    }

-- Normalization without zeros

MatrixPivots≁0 : Matrix F n m → Vector (Fin m) n → Set _
MatrixPivots≁0 xs v = ∀ i → Lookup≢0 (xs i) (v i)

AllRowsNormalized≁0 : Vector (Fin m) n → Set _
AllRowsNormalized≁0 = Monotonic₁ _<_ _<_

ColumnsZero≁0 : Matrix F n m → Vector (Fin m) n → Set _
ColumnsZero≁0 xs pivs = ∀ i j → i ≢ j → xs j (pivs i) ≈ 0#

record MatrixIsNormed≁0 (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor cIsNorm≁0
  field
    pivs         : Vector (Fin m) n
    mPivots      : MatrixPivots≁0 xs pivs
    pivsCrescent : AllRowsNormalized≁0 pivs
    columnsZero  : ColumnsZero≁0 xs pivs

record MatrixNormed≁0 (m n : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    xs       : Matrix F n m
    isNormed : MatrixIsNormed≁0 xs

  open MatrixIsNormed≁0 isNormed public

PivsOne≁0 : ∀ (xs : Matrix F n m) (pivs : Vector (Fin m) n) → Set _
PivsOne≁0 xs pivs = ∀ i → xs i (pivs i) ≈ 1#

PivsOne≁0⁺ : ∀ (xs : Matrix F n m) (pivs : Vector (Fin m ⁺) n) → Set _
PivsOne≁0⁺ xs pivs = ∀ i → All (λ j → xs i j ≈ 1#) (pivs i)

record MatrixIsNormed≁0≈1 (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor cIsNorm≁0≈1
  field
    isNormed : MatrixIsNormed≁0 xs

  open MatrixIsNormed≁0 isNormed public

  field
    pivsOne  : PivsOne≁0 xs pivs


record MatrixNormed≁0≈1 (m n : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    xs         : Matrix F n m
    isNormed≈1 : MatrixIsNormed≁0≈1 xs

  open MatrixIsNormed≁0≈1 isNormed≈1 public

record FromNormalization≁0 (xs : Matrix F n m) (p : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ys       : Matrix F p m
    ysNormed : MatrixIsNormed≁0 {n = p} ys
    xs≋ⱽys   : xs ≋ⱽ ys

  open MatrixIsNormed≁0 ysNormed public

record FromNormalization≁0≈1 (xs : Matrix F n m) (p : ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ys       : Matrix F p m
    ysNormed : MatrixIsNormed≁0≈1 ys
    xs≋ⱽys   : xs ≋ⱽ ys

  open MatrixIsNormed≁0≈1 ysNormed public

≈-norm : {xs ys : Matrix F n m} → (∀ i j → xs i j ≈ ys i j) → MatrixIsNormed≁0≈1 xs → MatrixIsNormed≁0≈1 ys
≈-norm {xs = xs} {ys} xs≈ys (cIsNorm≁0≈1 (cIsNorm≁0 pivs mPivots pivsCrescent columnsZero) pivsOne) =
  cIsNorm≁0≈1 (cIsNorm≁0 pivs mPivsYs pivsCrescent colsYs) pivsYsOne

  where

  ys≈xs : ∀ i j → ys i j ≈ xs i j
  ys≈xs i j = sym (xs≈ys i j)

  mPivsYs : MatrixPivots≁0 ys pivs
  proj₁ (mPivsYs i) = #-congʳ (xs≈ys i _) (mPivots i .proj₁)
  proj₂ (mPivsYs i) j ineq = trans (ys≈xs i j) $ mPivots i .proj₂ j ineq

  colsYs : ColumnsZero≁0 ys pivs
  colsYs i j i≢j = trans (ys≈xs _ _) $ columnsZero i j i≢j

  pivsYsOne : PivsOne≁0 ys pivs
  pivsYsOne i = trans (ys≈xs _ _) (pivsOne _)
