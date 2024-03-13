open import Algebra.DecidableField

module MatrixFuncNormalization.Definitions {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
open import Algebra
open import Algebra.Apartness
open import Data.Bool.Base
open import Data.List as L using (List)
open import Data.Product
open import Data.Nat.Base using (ℕ)
open import Data.Fin as F using (Fin)
open import Data.Vec.Functional
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Nullary
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps

open import Algebra.Matrix.Structures

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)

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

  αys⇒αxs : α isSolutionOf ys → α isSolutionOf xs
  αys⇒αxs = sameSolutions (_≋ⱽ_.fwd xs≋ⱽys)
