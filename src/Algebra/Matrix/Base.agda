module Algebra.Matrix.Base where

open import Level using (Level)
open import Function using (_$_)
open import Algebra
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Functional
open import Relation.Nullary

infixr 5 _++ⱽ_

private variable
  a : Level
  A : Set a
  m n p : ℕ

Matrix : Set a → (m n : ℕ) → Set a
Matrix A m n = Vector (Vector A n) m

_++ⱽ_ : Matrix A m n → Matrix A m p → Matrix A m (n ℕ.+ p)
_++ⱽ_ {n = n} xs ys i j = [ xs i , ys i ] (splitAt n j)

takeⱽ : ∀ n → Matrix A m (n ℕ.+ p) → Matrix A m n
takeⱽ _ = map $ take _

dropⱽ : ∀ n → Matrix A m (n ℕ.+ p) → Matrix A m p
dropⱽ _ = map $ drop _

swap : (p q : Fin n) → Op₁ (Matrix A n m)
swap p q M i with p ≟ i | q ≟ i
... | yes _ | _     = M q
... | no  _ | yes _ = M p
... | no  _ | no  _ = M i

flip : Matrix A n m → Matrix A n m
flip xs i j = xs (opposite i) (opposite j)
