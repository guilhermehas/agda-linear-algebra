open import Algebra

module Algebra.Module.Base {rr ℓr}
  (ring : Ring rr ℓr) where

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality as ≡ hiding (sym)

open Ring ring renaming (Carrier to R)

data VecOp (n : ℕ) : Set rr where
  swapOp  : (p q : Fin n) (p≢q : p ≢ q)         → VecOp n
  addCons : (p q : Fin n) (p≢q : p ≢ q) (r : R) → VecOp n
