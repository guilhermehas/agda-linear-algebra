module Fin.Properties where

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s; _∸_)
open import Relation.Binary.PropositionalEquality
open import Fin.Base

private variable
  m n : ℕ

toℕ-reduce≥ : ∀ (i : Fin (m ℕ.+ n)) (m≤n : m ℕ.≤ toℕ i) → toℕ (reduce≥ i m≤n) ≡ toℕ i ∸ m
toℕ-reduce≥ {ℕ.zero} i z≤n = refl
toℕ-reduce≥ {ℕ.suc m} (suc i) (s≤s m≤i) rewrite toℕ-reduce≥ i m≤i = refl

suc-reduce : ∀ (i : Fin (ℕ.suc n)) (0<i : ℕ.zero ℕ.< toℕ i) → suc (reduce≥ i 0<i) ≡ i
suc-reduce (suc i) 0<i = refl
