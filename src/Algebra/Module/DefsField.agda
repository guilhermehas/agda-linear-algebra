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

open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

open LeftModule leftModule renaming (Carrierᴹ to M)
open HeytingField hField renaming (Carrier to A)

private variable
  n : ℕ

IsLinearIndependent : Vector M n → Set _
IsLinearIndependent xs = Σ[ (ys by _) ∈ xs reaches 0ᴹ ] (∃ λ i → ys i # 0#)
