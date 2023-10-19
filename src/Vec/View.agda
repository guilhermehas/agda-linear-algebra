open import Relation.Binary

module Vec.View {a ℓ}
  (S : Setoid a ℓ)
  where

open import Level hiding (suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; s≤s)
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Vec
open import Data.Vec.Relation.Binary.Equality.Setoid S
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PI hiding (refl; lookup)
  renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open Setoid S renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym)

private variable
  m n p q : ℕ
  x y : A
  xs ys : Vec A n

data VecView (xs : Vec A (suc n)) (i : Fin (suc n)) : Set (a ⊔ ℓ) where
  view : {ys : Vec A (toℕ i)} {x : A} {zs : Vec A p} → ys ++ [ x ] ++ zs ≋ xs → VecView xs i

vec→VecView : (xs : Vec A (suc n)) (i : Fin (suc n)) → VecView xs i
vec→VecView (x ∷ xs) fzero = view {ys = []} ≋-refl
vec→VecView {suc n} (x ∷ xs) (fsuc i) with vec→VecView xs i
... | view {ys = ys} {y} {zs} eqn = view {ys = x ∷ ys} (_∷_ {A = A} ≈-refl eqn)

lookupVecView : ∀ {xs : Vec A n} i {ys : Vec A (toℕ i)} {x} {zs : Vec A p}
  → ys ++ [ x ] ++ zs ≋ xs
  → lookup xs i ≈ x
lookupVecView fzero {[]} (eqn :: _) = ≈-sym eqn
lookupVecView (fsuc i) {_ ∷ _} (_ :: eqn) = lookupVecView i eqn

changeVecView : ∀ {xs : Vec A n} i {ys : Vec A (toℕ i)} {x} {zs : Vec A p} y
  → ys ++ [ x ] ++ zs ≋ xs
  → ys ++ [ y ] ++ zs ≋ xs [ i ]≔ y
changeVecView fzero {[]} _ (_ :: eqn) = ≈-refl :: eqn
changeVecView (fsuc i) {a ∷ ys} y (x∼y :: eqn) = x∼y :: changeVecView i y eqn


data VecView2 (xs : Vec A (2 + n)) (i j : Fin (2 + n)) (i<j : i < j) : Set (a ⊔ ℓ) where
  view2 : {ys : Vec A (toℕ i)} {x : A} {zs : Vec A (toℕ j ∸ toℕ i ∸ 1)} {w : A} {ws : Vec A q}
    → ys ++ [ x ] ++ zs ++ [ w ] ++ ws ≋ xs → VecView2 xs i j i<j

vec→VecView2 : (xs : Vec A (2 + n)) {i j : Fin (2 + n)} (i<j : i < j) → VecView2 xs i j i<j
vec→VecView2 (x ∷ xs) {fzero} {fsuc j} i<j with vec→VecView xs j
... | view eqn = view2 {ys = []} (≈-refl :: eqn)
vec→VecView2 {n = ℕ.zero} (x ∷ y ∷ []) {fsuc fzero} {fsuc fzero} (s≤s ())
vec→VecView2 {n = suc n} (x ∷ xs) {fsuc i} {fsuc j} (s≤s i<j) with vec→VecView2 xs i<j
... | view2 eqn = view2 {ys = x ∷ _} (≈-refl :: eqn)

lookupVecView2ˡ : ∀ {xs : Vec A n} {i j : Fin n} (i<j : i < j)
  {ys : Vec A (toℕ i)} {x} {zs : Vec A (toℕ j ∸ toℕ i ∸ 1)} {w} {ws : Vec A q}
  → ys ++ [ x ] ++ zs ++ [ w ] ++ ws ≋ xs
  → lookup xs i ≈ x
lookupVecView2ˡ {i = fzero} _ {[]} (eqn :: _) = ≈-sym eqn
lookupVecView2ˡ {i = fsuc _} {fsuc _} (s≤s i<j) {_ ∷ _} (_ :: eqn) = lookupVecView2ˡ i<j eqn

lookupVecView2ʳ : ∀ {xs : Vec A n} {i j : Fin n} (i<j : i < j)
  {ys : Vec A (toℕ i)} {x} {zs : Vec A (toℕ j ∸ toℕ i ∸ 1)} {w} {ws : Vec A q}
  → ys ++ [ x ] ++ zs ++ [ w ] ++ ws ≋ xs
  → lookup xs j ≈ w
lookupVecView2ʳ {i = fzero} {fsuc j} _ {[]} (_ :: eqn) = lookupVecView j eqn
lookupVecView2ʳ {i = fsuc i} {fsuc j} (s≤s i<j) {x ∷ ys} (x∼y :: eqn) = lookupVecView2ʳ i<j eqn

changeVecView2ˡ : ∀ {xs : Vec A n} {i j : Fin n} (i<j : i < j)
  {ys : Vec A (toℕ i)} {x} {zs : Vec A (toℕ j ∸ toℕ i ∸ 1)} {w} {ws : Vec A q} y
  → ys ++ [ x ] ++ zs ++ [ w ] ++ ws ≋ xs
  → ys ++ [ y ] ++ zs ++ [ w ] ++ ws ≋ xs [ i ]≔ y
changeVecView2ˡ {i = fzero} i<j {[]} y (x∼y :: eqn) = ≈-refl :: eqn
changeVecView2ˡ {i = fsuc i} {fsuc j} (s≤s i<j) {x ∷ ys} y (x∼y :: eqn) = x∼y :: changeVecView2ˡ i<j y eqn

changeVecView2ʳ : ∀ {xs : Vec A n} {i j : Fin n} (i<j : i < j)
  {ys : Vec A (toℕ i)} {x} {zs : Vec A (toℕ j ∸ toℕ i ∸ 1)} {w} {ws : Vec A q} y
  → ys ++ [ x ] ++ zs ++ [ w ] ++ ws ≋ xs
  → ys ++ [ x ] ++ zs ++ [ y ] ++ ws ≋ xs [ j ]≔ y
changeVecView2ʳ {i = fzero} {fsuc j} _ {[]} y (x∼y :: eqn) = x∼y :: changeVecView j y eqn
changeVecView2ʳ {i = fsuc _} {fsuc _} (s≤s i<j) {_ ∷ _} y (x∼y :: eqn) = x∼y :: (changeVecView2ʳ i<j y eqn)
