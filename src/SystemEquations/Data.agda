open import Algebra.DecidableField

module SystemEquations.Data {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
open import Data.Empty
open import Data.Bool
open import Data.Unit.Polymorphic
open import Data.Nat hiding (_⊔_)
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Vec
open import Data.Vec.Functional using (fromVec; toVec)

open import Vec.Base
open import Algebra.MatrixData.Base

open DecidableField dField renaming (Carrier to F)
open import SystemEquations.Definitions dField as SE using ()
open import SystemEquations.UniqueSolution dField

private variable
  m n : ℕ

infix 6 _+span_

record Affine (p : ℕ) : Set c where
  constructor vAff
  field
    coeff    : Vec F p
    constant : F

VecAffine : (nVars freeVars : ℕ) → Set c
VecAffine nVars freeVars = Vec (Affine freeVars) nVars

unfoldConstants : VecAffine n m → Vec F n
unfoldConstants [] = []
unfoldConstants (vAff coeff constant ∷ xs) = constant ∷ unfoldConstants xs

unfoldVecs : VecAffine n m → Matrix F n m
unfoldVecs [] = []
unfoldVecs (vAff coeff constant ∷ xs) = coeff ∷ unfoldVecs xs

record AffineTranspose (nVars freeVars : ℕ) : Set c where
  constructor _+span_
  field
    constants : Vec F nVars
    coeffs    : Matrix F freeVars nVars

open AffineTranspose

vAff→vAffT : VecAffine n m → AffineTranspose n m
vAff→vAffT xs = unfoldConstants xs +span transpose (unfoldVecs xs)

record SystemEquations (rows cols : ℕ) : Set c where
  constructor system
  field
    A : Matrix F rows cols
    b : Vec F rows

data Solution (n : ℕ) : Set (c ⊔ ℓ₁) where
  sol   : ∀ p (affine : VecAffine n p) → Solution n
  noSol : Solution n

HasSolution? : Solution n → Bool
HasSolution? (sol _ _) = true
HasSolution? noSol = false

HasNoSolution? : Solution n → Bool
HasNoSolution? = not ∘ HasSolution?

HasNoSolution : Solution n → Set
HasNoSolution = T ∘ HasNoSolution?

HasUniqueSolution? : Solution n → Bool
HasUniqueSolution? (sol ℕ.zero affine) = true
HasUniqueSolution? (sol (ℕ.suc p) affine) = false
HasUniqueSolution? noSol = false

HasUniqueSolution : Solution n → Set
HasUniqueSolution = T ∘ HasUniqueSolution?

solve : SystemEquations n m → Solution m
solve se = help solF
  where
  open SystemEquations se

  seF = SE.system (matrixData→Fun A) (fromVec b)

  module SeF = SE.SystemEquations seF

  solF = solveUniqueSystemEquations seF

  help : SeF.Solution → Solution _
  help (SE.SystemEquations.sol p affine x) = sol p $ tabulate $ help2 ∘ affine
    where
    help2 : _ → _
    help2 (SE.vAff coeff constant) = vAff (toVec coeff) constant
  help (SE.SystemEquations.noSol _) = noSol

sizeSolutionT : Solution n → Set _
sizeSolutionT (sol _ _) = ℕ
sizeSolutionT noSol = ⊤

sizeSolution : (solution : Solution n) → sizeSolutionT solution
sizeSolution (sol p _) = p
sizeSolution noSol = _

solMComplexT : Solution m → Set _
solMComplexT {m} (sol p affine) = Matrix F p m
solMComplexT noSol = ⊤

solMComplex : (solution : Solution n) → solMComplexT solution
solMComplex (sol p affine) = coeffs $ vAff→vAffT affine
solMComplex noSol = _

solveComplex0 : (A : Matrix F n m) → solMComplexT $ solve $ system A $ repeat 0#
solveComplex0 A = solMComplex $ solve $ system A $ repeat 0#

solAllT : Solution m → Set c
solAllT {m} (sol ℕ.zero affine) = Vec F m
solAllT {m} (sol p@(ℕ.suc _) affine) = AffineTranspose m p
solAllT noSol = ⊤

solAll : (solt : Solution m) → solAllT solt
solAll (sol ℕ.zero affine) = unfoldConstants affine
solAll (sol (ℕ.suc p) affine) = vAff→vAffT affine
solAll noSol = _

solveAll : (A : Matrix F n m) (b : Vec F n) → solAllT $ solve $ system A b
solveAll A b = solAll $ solve $ system A b
