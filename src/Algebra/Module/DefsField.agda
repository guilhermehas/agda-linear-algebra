open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function

module Algebra.Module.DefsField
  {c ℓ₁ ℓ₂ mr ℓm}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (leftModule : LeftModule (CommutativeRing.ring
   $ HeytingCommutativeRing.commutativeRing
   $ HeytingField.heytingCommutativeRing hField) mr ℓm)
  where

open import Algebra.Module.Definition leftModule public

open import Level using (Level; _⊔_)
open import Data.Bool
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

open LeftModule leftModule renaming (Carrierᴹ to M)
open HeytingField hField renaming (Carrier to A)

private variable
  n : ℕ

IsLinearDependent : Vector M n → Set _
IsLinearDependent xs = Σ[ (ys by _) ∈ xs reaches 0ᴹ ] ∃ λ i → ys i # 0#

data LinearIndependent? (xs : Vector M n) : Bool → Set (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓm) where
  linDep : IsLinearDependent   xs → LinearIndependent? xs false
  linInd : IsLinearIndependent xs → LinearIndependent? xs true
