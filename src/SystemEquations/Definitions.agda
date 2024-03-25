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
open import MatrixFuncNormalization.NormAfter.Properties dField
  using (ColumnsZero)

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open MRing rawRing hiding (matOps→func)
open VRing rawRing using (_∙ⱽ_)
open PNorm
open PVec

private variable
  m n p rows cols : ℕ

-- This is the "syntax" of a affine function : Vector F p → Fn
record Affine (p : ℕ) : Set c where
  field
    coeff    : Vector F p
    constant : F

  eval : Vector F p → F
  eval vecs = vecs ∙ⱽ coeff + constant

-- This is the "syntax" of a collection of affine funtions
--   but also can represent all solutions of an eq. system
VecAffine : (nVars freeVars : ℕ) → Set c
VecAffine nVars freeVars = Vector (Affine freeVars) nVars

open Affine


getRow : (r : Fin rows) → Matrix F rows cols → Vector F cols
getRow r m = m r


record SystemEquations (rows cols : ℕ) : Set c where
  field
    A : Matrix F rows cols
    b : Vector F rows

  IsSolution : Vector F cols → Set ℓ₁
  IsSolution x = ∀ r → getRow r A ∙ⱽ x ≈ b r

  A++b : Matrix F rows (cols ℕ.+ 1)
  A++b = A ++ⱽ const ∘ b

  IsFamilySolution : VecAffine cols p → Set (c ⊔ ℓ₁)
  IsFamilySolution affine = ∀ vecs → IsSolution (λ i → eval (affine i) vecs)

-- findSolutions : x ≡ 0 × x ≡ 1 → ⊥
-- AllSolutionsInVec : (vecAffine : VecAffine m p) → IsSolution x → ∃ v such (vecAffine.eval v ≡ x)

vSol : VecAffine 2 1
vSol F.zero = record { coeff = (λ where F.zero → 1# + 1#) ; constant = 0# }
vSol (F.suc F.zero) = record { coeff = (λ where F.zero → 1#) ; constant = 0# }

A` : Matrix F 1 2
A` F.zero F.zero = 1#
A` F.zero (F.suc F.zero) = - (1# + 1#)

systemEquation : SystemEquations 1 2
systemEquation = record { A = A` ; b = λ _ → 0# }

open SystemEquations systemEquation

-- isSol : IsFamilySolution vSol
-- isSol vecs F.zero = {!!}

-- x - 2*y = 0

-- x = 2w → Affine coeff [2] constant 0
-- y = w  → Affine coeff [1] constant 0

-- ----------------

-- postulate 1ᴹ : Matrix A n n
embedUniqueSol : (nVars : ℕ) → VecAffine nVars 0 → SystemEquations nVars nVars
embedUniqueSol n va = record { A = 1ᴹ; b = λ r → constant (va r) }
{-
-- TODO (fix)
embed : (cols p : ℕ) → VecAffine cols p → SystemEquations (cols + p) cols
embed cols rows va = record {
  A = λ r c → coeff (va c) r ;
  b = λ r → constant (va {!r!}) }
  -- each Affine contributes one row of A and one element in b
-}
