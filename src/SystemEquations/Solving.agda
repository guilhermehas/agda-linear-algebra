open import Algebra.DecidableField

module SystemEquations.Solving {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as F
open import Data.Vec.Functional

open import Vector.Structures
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps′

open DecidableField dField
open HeytingField heytingField renaming (Carrier to F)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing
open import Algebra.Module.Instances.CommutativeRing commutativeRing

open module MD {n} = MDefinition (leftModule n)
open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)

private variable
  m n : ℕ

private
  lastFin : (n : ℕ) → Fin (n ℕ.+ 1)
  lastFin ℕ.zero = F.zero
  lastFin (ℕ.suc n) = suc (lastFin n)

  injF : Fin n → Fin (n ℕ.+ 1)
  injF F.zero = F.zero
  injF (suc i) = suc (injF i)

A++b⇒systemEquations : Matrix F n (m ℕ.+ 1) → SystemEquations n m
A++b⇒systemEquations xs = record { A = λ i j → xs i (injF j) ; b = λ i → xs i (lastFin _) }

open SystemEquations

sameSolutionsSE : (xs ys : Matrix F n (m ℕ.+ 1)) → xs ≋ⱽ ys → ∀ v
  → IsSolution (A++b⇒systemEquations xs) v
  → IsSolution (A++b⇒systemEquations ys) v
sameSolutionsSE xs ys xs≋ⱽys v isSolXs i = {!!}
