module Vector.Permutation.Properties where

open import Level
open import Function using (_∘_)
open import Function.Bundles using (Inverse)
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Fin.Permutation as ↭ hiding (↔⇒≡)
open import Data.Vec.Functional hiding (transpose; remove; insert)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; cong; module ≡-Reasoning)

open import Vector.Base
open import Vector.Permutation.Base

open ≡-Reasoning

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ
  xs ys zs : Vector A n
  x y : A

refl : xs ↭ xs
proj₁ refl = id
proj₂ refl i = ≡.refl

reflexive : xs ≡ ys → xs ↭ ys
reflexive ≡.refl = refl

sym : xs ↭ ys → ys ↭ xs
proj₁ (sym (xs↭ys , _)) = flip xs↭ys
proj₂ (sym {xs = xs} {ys = ys} (xs↭ys , xs↭ys≡)) i = begin
  ys (flip xs↭ys ⟨$⟩ʳ i)             ≡˘⟨ xs↭ys≡ _ ⟩
  xs (xs↭ys ⟨$⟩ʳ (flip xs↭ys ⟨$⟩ʳ i)) ≡⟨ cong xs (inverseʳ xs↭ys) ⟩
  xs i ∎

trans : xs ↭ ys → ys ↭ zs → xs ↭ zs
proj₁ (trans (xs↭ys , _) (ys↭zs , _))   = ys↭zs ∘ₚ xs↭ys
proj₂ (trans (_ , xs↭ys) (_ , ys↭zs)) _ = ≡.trans (xs↭ys _) (ys↭zs _)

prep : xs ↭ ys → x ∷ xs ↭ x ∷ ys
proj₁ (prep (xs↭ys , _)) = lift₀ xs↭ys
proj₂ (prep (_ , _)) zero        = ≡.refl
proj₂ (prep (_ , xs↭ys)) (suc i) = xs↭ys i

swapTwo : xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
proj₁ (swapTwo (xs↭ys , _)) = transpose 0F 1F ∘ₚ lift₀ (lift₀ xs↭ys)
proj₂ (swapTwo (_ , xs↭ys)) zero = ≡.refl
proj₂ (swapTwo (_ , xs↭ys)) (suc zero) = ≡.refl
proj₂ (swapTwo (_ , xs↭ys)) (suc (suc i)) = xs↭ys i

↔⇒≡ : xs ↭ ys → length xs ≡ length ys
↔⇒≡ (xs↭ys , _) = ≡.sym (↭.↔⇒≡ xs↭ys)

drop-mid : ∀ {x} (ws xs : Vector A m) {ys zs : Vector A n} →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
proj₁ (drop-mid ws xs (ρ , _)) = remove {!!} {!ρ!}
proj₂ (drop-mid ws xs perm) = {!!}


insert-mid : ∀ x (ws xs : Vector A m) {ys zs : Vector A n} →
           ws ++ ys ↭ xs ++ zs →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs
proj₁ (insert-mid x ws xs (ρ , _)) = {!insert!}
proj₂ (insert-mid x ws xs (ρ , _)) = {!!}
