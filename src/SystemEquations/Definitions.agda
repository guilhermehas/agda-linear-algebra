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
    m n p : ℕ

  record MatrixNormed (xs : Matrix F n m) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      pivs         : Vector (Fin m ⁺) n
      mPivots      : MatrixPivots xs pivs
      pivsCrescent : AllRowsNormalized pivs
      columnsZero  : ColumnsZero xs pivs

  record Polynomial (p : ℕ) : Set c where
    field
      poly : Vector F p
      constant : F

  VecPolynomial : (n p : ℕ) → Set c
  VecPolynomial n p = Vector (Polynomial p) n

  record SystemEquations (m n : ℕ) : Set c where
    field
      A : Matrix F n m
      b : Vector F n

    IsSolution : Vector F m → Set ℓ₁
    IsSolution x = ∀ row → (∑ (λ i → A row i * x i) ≈ b row)

    A++b : Matrix F n (m ℕ.+ 1)
    A++b = A ++ⱽ const ∘ b

    IsFamilySolution : VecPolynomial m p → Set (c ⊔ ℓ₁)
    IsFamilySolution vPoly = ∀ vecs → IsSolution (vSol vecs)
      where
      vSol : (vecs : Vector F _) → Vector F m
      vSol vecs i = ∑ (λ j → vecs j * poly j) + constant
        where open Polynomial (vPoly i)
