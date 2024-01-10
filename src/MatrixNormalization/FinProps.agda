module MatrixNormalization.FinProps where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function using (_$_)
open import Data.Nat as ℕ using (ℕ; suc; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Fin
open import Data.Fin.Properties as F
open import Relation.Binary.PropositionalEquality

open import lbry

private variable
  ℓ ℓ₁ : Level
  n : ℕ

record FinProps {ℓ₁} {ℓ₂} (A : Set ℓ) (n : ℕ) : Set (lsuc $ ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    Pij : (i j : Fin (suc n)) .(i≤j : i ≤ j) (a : A) → Set ℓ₁
    Pi : (i : Fin (suc n)) (a : A) → Set ℓ₁
    P : (a : A) → Set ℓ₁

    Pab : ∀ (i j : Fin (suc n)) .(i≢j : i ≢ j) (a b : A) → Set ℓ₂

    Pij→Pi : ∀ (i : Fin (ℕ.suc n)) a (pij : Pij i (fromℕ _) (≤fromℕ _) a) → Pi i a
    Pi→P : ∀ a (pi : Pi (fromℕ n) a) → P a
    Pi→Pii : ∀ (i : Fin n) a (pi : Pi (inject₁ i) a) → Pij (suc i) (suc i) F.≤-refl a

    Ps : ∀ i (j : Fin n) .(i≤j : i ≤ j) a b
      (pij : Pij i (inject₁ j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) a)
      (pab : Pab i (suc j) (F.<⇒≢ (s≤s i≤j)) a b) → Pij i (suc j) (m≤n⇒m≤1+n i≤j) b

    P00 : ∀ a → Pij zero zero ℕ.z≤n a

record FinPropsInv (A : Set ℓ) (n : ℕ) : Set (lsuc ℓ) where
  field
    Pij : (i j : Fin (suc n)) .(i≥j : i ≥ j) (a : A) → Set ℓ
    Pi : (i : Fin (suc n)) (a : A) → Set ℓ
    P : (a : A) → Set ℓ

    Pab : ∀ (i j : Fin (suc n)) .(i>j : i > j) (a b : A) → Set ℓ

    Pij→Pi : ∀ (i : Fin (ℕ.suc n)) a (pij : Pij i zero z≤n a) → Pi i a
    Pi→P : ∀ a (pi : Pi zero a) → P a
    Pi→Pii : ∀ (i : Fin n) a (pi : Pi (suc i) a) → Pij (inject₁ i) (inject₁ i) F.≤-refl a

    Ppred : ∀ i (j : Fin n) .(i>j : i > j) a b
      (pij : Pij i (suc j) i>j a)
      (pab : Pab i (inject₁ j) (i>j→i>injJ i>j) a b)
      → Pij i (inject₁ j) (i>j→i≥j i>j) b

    Pnn : ∀ a → Pij (fromℕ _) (fromℕ _) F.≤-refl a
