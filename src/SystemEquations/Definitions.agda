open import Algebra.DecidableField

module SystemEquations.Definitions {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

  open import Level
  open import Algebra
  open import Algebra.Apartness
  open import Data.Nat.Base using (ℕ)
  open import Data.Vec.Functional
  open import Data.Fin as F using (Fin)
  open import Relation.Nullary.Construct.Add.Supremum

  open import Algebra.Matrix.Structures

  open DecidableField dField renaming (Carrier to F; heytingField to hField)
  open HeytingField hField using (heytingCommutativeRing)
  open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
  open CommutativeRing commutativeRing using (rawRing; ring)
  open MRing rawRing hiding (matOps→func)

  open import MatrixFuncNormalization.normBef dField
  open import MatrixFuncNormalization.NormAfter.PropsFlip dField
    hiding (module PNorm)
  open import MatrixFuncNormalization.NormAfter.Properties dField
    using (ColumnsZero)

  open PNorm

  private variable
    m n : ℕ

  record MatrixNormed (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      pivs         : Vector (Fin m ⁺) n
      mPivots      : MatrixPivots xs pivs
      pivsCrescent : AllRowsNormalized pivs
      columnsZero  : ColumnsZero xs pivs
