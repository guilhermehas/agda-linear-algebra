open import Algebra.Apartness
open import Relation.Binary
open import Algebra.DecidableField

module MatrixFuncNormalization.MainTheo {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

  open import Level
  open import Function
  open import Algebra
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

  record MatrixNorm (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ys           : Matrix F n m
      pivs         : Vector (Fin m ⁺) n
      mPivots      : MatrixPivots ys pivs
      xs≈ⱽys       : xs ≈ⱽ ys
      pivsCrescent : AllRowsNormalized pivs
      columnsZero  : ColumnsZero ys pivs

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

  mainTheo : (xs : Matrix F n m) → MatrixNorm xs
  mainTheo xs = let ys , pivs , mPivs , xs≈ⱽys , colsZero , pivsCrescent = allTheoremsTogether xs in
    record
     { ys           = ys
     ; pivs         = pivs
     ; mPivots      = mPivs
     ; xs≈ⱽys       = xs≈ⱽys
     ; pivsCrescent = pivsCrescent
     ; columnsZero  = colsZero
     }
