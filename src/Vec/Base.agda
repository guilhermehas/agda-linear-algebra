open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

module Vec.Base where

private variable
  ℓ : Level
  A : Set ℓ
  n : ℕ

swapV : (xs : Vec A n) (i j : Fin n) → Vec A n
swapV xs i j = xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i

repeat : A → Vec A n
repeat {n = ℕ.zero} _ = []
repeat {n = ℕ.suc n} x = x ∷ repeat x
