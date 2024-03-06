open import Algebra.DecidableField

module SystemEquations.Definitions {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

  open import Level
  open import Function
  open import Algebra
  open import Algebra.Apartness
  open import Data.Nat.Base as ℕ using (ℕ)
  open import Data.Vec.Functional
  open import Data.Fin as F using (Fin)
  open import Relation.Nullary.Construct.Add.Supremum

  open import Algebra.Matrix.Structures
  open import Vector.Structures

  open import MatrixFuncNormalization.normBef dField
  open import MatrixFuncNormalization.NormAfter.PropsFlip dField
    hiding (module PNorm)
  open import MatrixFuncNormalization.NormAfter.Properties dField
    using (ColumnsZero)

  open DecidableField dField renaming (Carrier to F; heytingField to hField)
  open HeytingField hField using (heytingCommutativeRing)
  open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
  open CommutativeRing commutativeRing using (rawRing; ring)
  open MRing rawRing hiding (matOps→func)
  open VRing rawRing using (_∙ⱽ_)
  open PNorm

  private variable
    m n p : ℕ

  record MatrixNormed (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      pivs         : Vector (Fin m ⁺) n
      mPivots      : MatrixPivots xs pivs
      pivsCrescent : AllRowsNormalized pivs
      columnsZero  : ColumnsZero xs pivs

  record Affine (p : ℕ) : Set c where
    field
      coeff    : Vector F p
      constant : F

    eval : Vector F p → F
    eval vecs = vecs ∙ⱽ coeff + constant

  VecAffine : (n p : ℕ) → Set c
  VecAffine n p = Vector (Affine p) n

  open Affine

  record SystemEquations (m n : ℕ) : Set c where
    field
      A : Matrix F n m
      b : Vector F n

    IsSolution : Vector F m → Set ℓ₁
    IsSolution x = ∀ i → A i ∙ⱽ x ≈ b i

    A++b : Matrix F n (m ℕ.+ 1)
    A++b = A ++ⱽ const ∘ b

    IsFamilySolution : VecAffine m p → Set (c ⊔ ℓ₁)
    IsFamilySolution affine = ∀ vecs → IsSolution (λ i → eval (affine i) vecs)

  -- findSolutions : x ≡ 0 × x ≡ 1 → ⊥
  -- AllSolutionsInVec : (vecAffine : VecAffine m p) → IsSolution x → ∃ v such (vecAffine.eval v ≡ x)

  vSol : VecAffine 2 1
  vSol F.zero = record { coeff = (λ where F.zero → 1# + 1#) ; constant = 0# }
  vSol (F.suc F.zero) = record { coeff = (λ where F.zero → 1#) ; constant = 0# }

  A` : Matrix F 1 2
  A` F.zero F.zero = 1#
  A` F.zero (F.suc F.zero) = - (1# + 1#)

  systemEquation : SystemEquations 2 1
  systemEquation = record { A = A` ; b = λ _ → 0# }

  open SystemEquations systemEquation

  -- isSol : IsFamilySolution vSol
  -- isSol vecs F.zero = {!!}

  -- x - 2*y = 0

  -- x = 2w -> Affine coeff [2] constant 0
  -- y = w  -> Affine coeff [1] constant 0
