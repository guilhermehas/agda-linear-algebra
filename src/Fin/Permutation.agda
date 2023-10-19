module Fin.Permutation where

open import Function as F hiding (id)
open import Data.Nat as ℕ using (ℕ; _∸_; _+_; _<?_; _≤_; _<_; z≤n)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Fin.Base hiding (_+_; _≤_; _<_)
open import Data.Fin.Properties hiding (_<?_; ≤-trans; ≤-refl)
open import Data.Fin.Permutation
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open ≡-Reasoning

private variable
  m n : ℕ

shift : Fin n → Permutation′ n
shift {ℕ.zero} i = id
shift n@{ℕ.suc n′} i = permutation to from to∘from from∘to
  where
  to : Fin n → Fin n
  to k = fromℕ< $ m%n<n (toℕ k + toℕ i) n

  from : Fin n → Fin n
  from k = fromℕ< $ m%n<n (n + toℕ k ∸ toℕ i) n

  to∘from : StrictlyInverseˡ _≡_ to from
  to∘from k = begin
    fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n (n + toℕ k ∸ toℕ i) n)) + toℕ i) n)
      ≡⟨ cong (λ x → fromℕ< (m%n<n (x + toℕ i) n)) toFrom<≡ ⟩
    fromℕ< (m%n<n ((n + toℕ k ∸ toℕ i) % n + toℕ i) n) ≡⟨ fromℕ<-cong _ _ same% _ _ ⟩
    fromℕ< (m%n<n (n + toℕ k ∸ toℕ i + toℕ i) n) ≡⟨ fromℕ<-cong _ _ sameN _ _ ⟩
    fromℕ< (m%n<n (toℕ k) n) ≡⟨ fromℕ<-cong (toℕ k % n) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) n) (toℕ<n k) ⟩
    fromℕ< (toℕ<n k) ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
    k ∎
    where

    toFrom<≡ : toℕ (fromℕ< (m%n<n (n + toℕ k ∸ toℕ i) n)) ≡ (n + toℕ k ∸ toℕ i) % n
    toFrom<≡ = toℕ-fromℕ< (m%n<n (n + toℕ k ∸ toℕ i) n)

    same% = begin
      ((n + toℕ k ∸ toℕ i) % n + toℕ i) % n     ≡˘⟨ cong (λ x → ((n + toℕ k ∸ toℕ i) % n + x) % n) (m<n⇒m%n≡m (toℕ<n i)) ⟩
      ((n + toℕ k ∸ toℕ i) % n + toℕ i % n) % n ≡˘⟨ %-distribˡ-+ (n + toℕ k ∸ toℕ i) (toℕ i) n ⟩
      (n + toℕ k ∸ toℕ i + toℕ i) % n ∎

    i<n+k : toℕ i ≤ n + toℕ k
    i<n+k = ≤-trans (toℕ≤n i) (m≤m+n _ _)

    sameN = begin
      (n + toℕ k ∸ toℕ i + toℕ i) % n ≡⟨ cong (_% n) (m∸n+n≡m i<n+k) ⟩
      (n + toℕ k) % n ≡⟨ cong (_% n) (+-comm n _) ⟩
      (toℕ k + n) % n ≡⟨ [m+n]%n≡m%n (toℕ k) n ⟩
      toℕ k % n ∎


  from∘to : StrictlyInverseʳ _≡_ to from
  from∘to k = begin
    fromℕ< (m%n<n (n + toℕ (fromℕ< $ m%n<n (toℕ k + toℕ i) n) ∸ toℕ i) n)
      ≡⟨ cong (λ x → fromℕ< (m%n<n (n + x ∸ toℕ i) n)) (toℕ-fromℕ< _) ⟩
    fromℕ< (m%n<n (n + (toℕ k + toℕ i) % n ∸ toℕ i) n) ≡⟨ fromℕ<-cong _ _ helper _ _ ⟩
    fromℕ< (toℕ<n k) ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
    k ∎

    where

    aux : ∀ i → (n ∸ toℕ i + (toℕ k + toℕ i) % n) % n ≡ toℕ k
    aux zero = begin
      (n + (toℕ k + ℕ.zero) % n) % n ≡⟨ cong (_% n) (trans (+-comm n _) (cong (λ x → x % n + n) (+-identityʳ (toℕ k)))) ⟩
      (toℕ k  % n + n) % n ≡⟨ [m+n]%n≡m%n ((toℕ k) % n) n ⟩
      toℕ k % n % n ≡⟨ m%n%n≡m%n (toℕ k) n ⟩
      toℕ k % n ≡⟨ m<n⇒m%n≡m (toℕ<n k) ⟩
      toℕ k ∎
    aux i@(suc i′) = begin
      (n ∸ toℕ i + (toℕ k + toℕ i) % n) % n ≡˘⟨ cong (λ x → (x + (toℕ k + toℕ i) % n) % n) (m<n⇒m%n≡m n-i<n) ⟩
      ((n ∸ toℕ i) % n + (toℕ k + toℕ i) % n) % n ≡˘⟨ %-distribˡ-+ (n ∸ toℕ i) (toℕ k + toℕ i) n ⟩
      ((n ∸ toℕ i) + (toℕ k + toℕ i)) % n ≡˘⟨ cong (_% n) (+-∸-comm (toℕ k + toℕ i) (toℕ≤n i)) ⟩
      (n + (toℕ k + toℕ i) ∸ toℕ i) % n ≡˘⟨ cong (λ x → (x ∸ toℕ i) % n) (+-assoc n _ _)  ⟩
      (n + toℕ k + toℕ i ∸ toℕ i) % n ≡⟨ cong (_% n) (m+n∸n≡m (n + toℕ k) (toℕ i)) ⟩
      (n + toℕ k) % n ≡⟨ cong (_% n) (+-comm n _) ⟩
      (toℕ k + n) % n ≡⟨ [m+n]%n≡m%n (toℕ k) n ⟩
      toℕ k % n ≡⟨ m<n⇒m%n≡m (toℕ<n k) ⟩
      toℕ k ∎
      where
      n-i<n : n′ ∸ toℕ i′ < n
      n-i<n = <-transʳ (m∸n≤m n′ (toℕ i′)) ≤-refl

    helper = begin
      (n + (toℕ k + toℕ i) % n ∸ toℕ i) % n ≡⟨ cong (_% n) (+-∸-comm ((toℕ k + toℕ i) % n) (toℕ≤n i)) ⟩
      (n ∸ toℕ i + (toℕ k + toℕ i) % n) % n ≡⟨ aux i ⟩
      toℕ k ∎
