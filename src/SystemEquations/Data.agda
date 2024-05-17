open import Algebra.DecidableField

module SystemEquations.Data {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
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

sizeSolutionJust : Solution n → Maybe ℕ
sizeSolutionJust (sol p affine) = just p
sizeSolutionJust noSol = nothing

sizeSolution : (solution : Solution n) → From-just $ sizeSolutionJust solution
sizeSolution = from-just ∘ sizeSolutionJust

vecAffSolutionJust : Solution n → Maybe $ ∃ $ VecAffine n
vecAffSolutionJust (sol p affine) = just $ p , affine
vecAffSolutionJust noSol          = nothing

vecAffSolution : (solution : Solution n) → From-just $ vecAffSolutionJust solution
vecAffSolution = from-just ∘ vecAffSolutionJust

vecSimpleSolutionJust : Solution n → Maybe $ Vec F n
vecSimpleSolutionJust (sol ℕ.zero affine) =  just (unfoldConstants affine)
vecSimpleSolutionJust (sol (ℕ.suc p) affine) = nothing
vecSimpleSolutionJust noSol = nothing

vecSimpleSolution : (solution : Solution n) → From-just $ vecSimpleSolutionJust solution
vecSimpleSolution = from-just ∘ vecSimpleSolutionJust

vecSpanSolutionJust : Solution n → Maybe $ ∃ $ AffineTranspose n
vecSpanSolutionJust (sol p affine) = just $ _ , vAff→vAffT affine
vecSpanSolutionJust noSol = nothing

matrixSolutionJust : Solution n → Maybe $ ∃ $ flip (Matrix F) n
matrixSolutionJust (sol p affine) = just $ _ , (coeffs $ vAff→vAffT affine)
matrixSolutionJust noSol = nothing

private
  From-just-vec : Maybe $ ∃ $ AffineTranspose n → Set _
  From-just-vec {n} (just (p , _)) = AffineTranspose n p
  From-just-vec nothing = ⊤

  from-just-vec : (x : Maybe (∃ $ AffineTranspose n)) → From-just-vec x
  from-just-vec (just (_ , x)) = x
  from-just-vec nothing  = _

  From-just-matrix : Maybe $ ∃ $ flip (Matrix F) n → Set _
  From-just-matrix {n} (just (m , _)) = Matrix F m n
  From-just-matrix nothing = ⊤

  from-just-matrix : (x : Maybe (∃ $ flip (Matrix F) n)) → From-just-matrix x
  from-just-matrix (just (_ , x)) = x
  from-just-matrix nothing  = _


vecComplexSolution : (solution : Solution n) → From-just-vec $ vecSpanSolutionJust solution
vecComplexSolution = from-just-vec ∘ vecSpanSolutionJust

solveComplexSE : (se : SystemEquations n m) → From-just-vec $ vecSpanSolutionJust (solve se)
solveComplexSE = vecComplexSolution ∘ solve

solveComplex : (A : Matrix F n m) (b : Vec F n) → From-just-vec $ vecSpanSolutionJust $ solve $ system A b
solveComplex A b = solveComplexSE $ system A b

solveComplex0 : (A : Matrix F n m) → From-just-matrix $ matrixSolutionJust $ solve $ system A (repeat 0#)
solveComplex0 A = from-just-matrix (matrixSolutionJust $ solve $ system A (repeat 0#))
