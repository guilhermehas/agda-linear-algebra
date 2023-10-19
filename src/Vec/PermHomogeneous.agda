module Vec.PermHomogeneous where

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ)
open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Relation.Binary

private variable
  ℓ r : Level
  A : Set ℓ
  m n : ℕ
  x y x′ y′ : A
  xs ys zs : Vec A n

data Permutation {A : Set ℓ} (R : Rel A r) : Vec A m → Vec A n → Set (ℓ ⊔ r) where
  refl  : Pointwise R xs ys → Permutation R xs ys
  prep  : (eq : R x y) → Permutation R xs ys → Permutation R (x ∷ xs) (y ∷ ys)
  swap  : (eq₁ : R x x′) (eq₂ : R y y′) → Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
  trans : Permutation R xs ys → Permutation R ys zs → Permutation R xs zs
