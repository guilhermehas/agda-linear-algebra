open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.MainTheo {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

  open import Level
  open import Function
  open import Algebra
  open import Algebra.Matrix
  open import Data.Bool.Base
  open import Data.List as L using (List)
  open import Data.Product
  open import Data.Nat.Base using (ℕ)
  open import Data.Fin as F using (Fin)
  open import Data.Vec.Functional
  open import Relation.Nullary.Construct.Add.Supremum
  open import Relation.Nullary

  open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
  open CommutativeRing commutativeRing using (rawRing; ring)

  open import MatrixFuncNormalization.normBef hField _≟_
  open import MatrixFuncNormalization.NormAfter.PropsFlip hField _≟_
    hiding (module PNorm)
  open import MatrixFuncNormalization.NormAfter.Properties hField _≟_
    using (ColumnsZero)
  open import Algebra.Module.Base ring

  open PVec
  open PNorm

  private variable
    m n p : ℕ

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
    inverseMatrix = reproduceOperations (λ i j → if isYes (i F.≟ j) then 1# else 0#)


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
