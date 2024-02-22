open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.MainTheo {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

  open import Level
  open import Algebra.Matrix
  open import Data.Product
  open import Data.Nat.Base using (ℕ)
  open import Data.Fin.Base
  open import Data.Vec.Functional
  open import Relation.Nullary.Construct.Add.Supremum


  open import MatrixFuncNormalization.normBef hField _≟_
  open import MatrixFuncNormalization.NormAfter.PropsFlip hField _≟_
  open import MatrixFuncNormalization.NormAfter.Properties hField _≟_ using (ColumnsZero)

  open PVec
  open PNorm

  private variable
    m n : ℕ

  record MatrixNorm (xs : Matrix F n m) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ys           : Matrix F n m
      pivs         : Vector (Fin m ⁺) n
      mPivots      : MatrixPivots ys pivs
      xs≈ⱽys       : xs ≈ⱽ ys
      pivsCrescent : AllRowsNormalized pivs
      columnsZero  : ColumnsZero ys pivs

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
