open import Algebra.DecidableField

module SystemEquations.Data {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level
open import Function
open import Data.Nat hiding (_⊔_)
open import Data.Maybe
open import Data.Product
open import Data.Vec
open import Data.Vec.Functional using (fromVec; toVec)

open import Algebra.MatrixData.Base

open DecidableField dField renaming (Carrier to F)
open import SystemEquations.Definitions dField as SE using ()
open import SystemEquations.UniqueSolution dField

private variable
  m n : ℕ

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
vecSimpleSolutionJust (sol ℕ.zero affine) = just (unfoldConstants affine)
vecSimpleSolutionJust (sol (ℕ.suc p) affine) = nothing
vecSimpleSolutionJust noSol = nothing

vecSimpleSolution : (solution : Solution n) → From-just $ vecSimpleSolutionJust solution
vecSimpleSolution = from-just ∘ vecSimpleSolutionJust
