open import Algebra.DecidableField

module SystemEquations.Solving {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as F using (Fin; suc)
open import Data.Fin.Patterns
open import Data.Vec.Functional

open import Vector.Structures
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps′

open DecidableField dField renaming (Carrier to F)
open HeytingField heytingField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open import Algebra.Properties.Ring ring
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing using (Matrix)
open import Algebra.Module.Instances.CommutativeRing commutativeRing
open import Data.Vec.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid

open module MD {n} = MDefinition (leftModule n)
open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)

private variable
  m n : ℕ

private
  lastFin : (n : ℕ) → Fin (n ℕ.+ 1)
  lastFin ℕ.zero = 0F
  lastFin (ℕ.suc n) = suc (lastFin n)

  injF : Fin n → Fin (n ℕ.+ 1)
  injF 0F = 0F
  injF (suc i) = suc (injF i)

  add-1 : Vector F n → Vector F (n ℕ.+ 1)
  add-1 {ℕ.zero} v _ = - 1#
  add-1 {ℕ.suc n} v 0F = v 0F
  add-1 {ℕ.suc n} v (suc i) = add-1 (tail v) i

A++b⇒systemEquations : Matrix F n (m ℕ.+ 1) → SystemEquations n m
A++b⇒systemEquations xs = record { A = λ i j → xs i (injF j) ; b = λ i → xs i (lastFin _) }

module _ where
  open SystemEquations

  sameSolutionsSE : {sx sy : SystemEquations n m}  → A++b sy ⊆ⱽ A++b sx
    → ∀ v → IsSolutionA++b sx v → IsSolutionA++b sy v
  sameSolutionsSE sy⊆ⱽsx _ = sameSolutions sy⊆ⱽsx

sameSolutionsA++b : ∀ {sx : SystemEquations n m} {v}
  (open SystemEquations sx)
  → IsSolutionA++b $ add-1 v → IsSolution v
sameSolutionsA++b {m = ℕ.zero} {sx = sx} {v} sv i = begin
  0#            ≈˘⟨ -0#≈0# ⟩
  - 0#          ≈˘⟨ -‿cong (sv i 0F) ⟩
  - (- 1# * b i) ≈⟨ -‿cong (-1*x≈-x (b i)) ⟩
  - (- b i)      ≈⟨ -‿involutive (b i) ⟩
  b i ∎
  where
  open SystemEquations sx

sameSolutionsA++b {m = ℕ.suc m} {sx = sx} {v} sv i = begin
  A i ∙ⱽ v ≈⟨ {!sv i 0F!} ⟩
  b i ∎
  where open SystemEquations sx
