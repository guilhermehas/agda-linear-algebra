open import Algebra.DecidableField

module SystemEquations.Definitions {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
open import Algebra
open import Algebra.Apartness
open import Data.Product
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Vec.Functional
open import Data.Fin as F using (Fin)
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Nullary
import Algebra.Module.Definition as MDef′

open import Algebra.Matrix.Structures
open import Vector.Structures

open import MatrixFuncNormalization.normBef dField
open import MatrixFuncNormalization.NormAfter.Properties dField
  using (ColumnsZero)

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open import Algebra.Module.PropsVec commutativeRing hiding (module MDef′)
open MRing rawRing hiding (matOps→func)
open VRing rawRing using (_∙ⱽ_)
open PNorm
open PVec
open module MDef {n} = MDef′ (leftModule n)

private variable
  m n p rows cols : ℕ

-- This is the "syntax" of a affine function : Vector F p → Fn
record Affine (p : ℕ) : Set c where
  constructor vAff
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
  constructor system
  field
    A : Matrix F rows cols
    b : Vector F rows

  IsSolution : Vector F cols → Set ℓ₁
  IsSolution x = ∀ r → A r ∙ⱽ x ≈ b r

  A++b : Matrix F rows (ℕ.suc cols)
  A++b = A ++v b

  IsFamilySolution : VecAffine cols p → Set (c ⊔ ℓ₁)
  IsFamilySolution affine = ∀ vecs → IsSolution (λ i → eval (affine i) vecs)

  IsSolutionA++b : Vector F _ → Set _
  IsSolutionA++b = _isSolutionOf A++b

  A≈0∧b#0I : Fin _ → Set _
  A≈0∧b#0I i = A i ≋ 0ⱽ × b i # 0#

  A≈0∧b#0 : Set _
  A≈0∧b#0 = ∃ A≈0∧b#0I

  data Solution (p : ℕ) : Set (c ⊔ ℓ₁) where
    sol : ∀ {affine} → IsFamilySolution {p = p} affine → Solution p
    noSol : (∀ {v} → ¬ IsSolution v) → Solution p

  open Solution public


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
