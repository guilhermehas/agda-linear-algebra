module Vector.Writes where

open import Level using (Level)
open import Function
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Fin
open import Data.Vec.Functional hiding ([]; _∷_)
open import Data.Vec hiding (_[_]≔_)
open import Algebra

open import Vector.Base

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ

substitute : (substitutes : Vec (Fin n × A) m) → Op₁ $ Vector A n
substitute = foldr′ (λ (i , v) f xs → f (xs [ i ]≔ v)) id

swapSubstitutes : (xs : Vector A n) (i j : Fin n) → Vec (Fin n × A) 2
swapSubstitutes xs i j = ((i , xs j)) ∷ (j , xs i) ∷ []
