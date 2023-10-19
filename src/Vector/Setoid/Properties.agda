open import Level using (Level; levelOfType)
open import Function
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.Sum
open import Data.Fin
open import Data.Vec.Functional
open import Data.Vec.Functional.Properties hiding (++-cong)
open import Data.Vec.Functional.Relation.Binary.Pointwise
open import Relation.Binary.PropositionalEquality as ≡ hiding (refl)
open import Relation.Binary
open import Relation.Nullary

open import Vector.Base using (swapV)

module Vector.Setoid.Properties {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid S
open import Relation.Binary.Reasoning.Setoid S

private variable
  m n : ℕ

module _ {m} {ys ys‵ : Vector A m} where

  ++-cong : ∀ {n} (xs xs‵ : Vector A n) →
            xs ≋ xs‵ → ys ≋ ys‵ → (xs ++ ys) ≋ (xs‵ ++ ys‵)
  ++-cong {n} xs xs‵ eq₁ eq₂ i with toℕ i ℕ.<? n
  ... | yes i<n = begin
    (xs ++ ys) i      ≡⟨ lookup-++-< xs ys i i<n ⟩
    xs (fromℕ< i<n)   ≈⟨ eq₁ (fromℕ< i<n) ⟩
    xs‵ (fromℕ< i<n)  ≡˘⟨ lookup-++-< xs‵ ys‵ i i<n ⟩
    (xs‵ ++ ys‵) i    ∎
  ... | no i≮n = begin
    (xs ++ ys) i               ≡⟨ lookup-++-≥ xs ys i (ℕ.≮⇒≥ i≮n) ⟩
    ys (reduce≥ i (ℕ.≮⇒≥ i≮n))   ≈⟨ eq₂ (reduce≥ i (ℕ.≮⇒≥ i≮n)) ⟩
    ys‵ (reduce≥ i (ℕ.≮⇒≥ i≮n))  ≡˘⟨ lookup-++-≥ xs‵ ys‵ i (ℕ.≮⇒≥ i≮n) ⟩
    (xs‵ ++ ys‵) i             ∎

module _ {m} {ys : Vector A m} where

  ++-congʳ : ∀ {n} (xs xs‵ : Vector A n) →
            xs ≋ xs‵ → (xs ++ ys) ≋ (xs‵ ++ ys)
  ++-congʳ {n} xs xs‵ eq = ++-cong xs xs‵ eq ≋-refl
