module Vec.Permutation {a} {A : Set a} where

open import Data.Nat using (ℕ)
open import Data.Vec
open import Relation.Binary

private variable
  n : ℕ
  xs ys zs : Vec A n

infix 3 _↭_

data _↭_ : Rel (Vec A n) a where
  refl  :         xs ↭ xs
  prep  : ∀ x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans :         xs ↭ ys → ys ↭ zs → xs ↭ zs
