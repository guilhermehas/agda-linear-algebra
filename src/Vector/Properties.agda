module Vector.Properties where

open import Level using (Level)
open import Function
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Sum
open import Data.Bool using (Bool; T; false; true)
open import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Vec.Functional
open import Data.Vec.Functional.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Vector.Base

open ≡-Reasoning

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ

tail++same : (xs : Vector A (ℕ.suc m)) (ys : Vector A n) → tail (xs ++ ys) ≗ (tail xs ++ ys)
tail++same {m = m} _ _ i with splitAt m i
... | inj₁ _ = refl
... | inj₂ _ = refl

head++tail≡id : (xs : Vector A (ℕ.suc n)) → (head xs ∷ tail xs) ≗ xs
head++tail≡id xs zero = refl
head++tail≡id xs (suc i) = refl

++-split : ∀ x (xs : Vector A m) (ys : Vector A n)
  → ((x ∷ xs) ++ ys) ≗ (x ∷ xs ++ ys)
++-split x xs ys zero = refl
++-split {m = m} x xs ys (suc i) with splitAt m i
... | inj₁ _ = refl
... | inj₂ _ = refl

swapCons : ∀ x (xs : Vector A n) (i j : Fin n) →
  swapV (x ∷ xs) (suc i) (suc j) ≗ (x ∷ swapV xs i j)
swapCons _ _ _ _ zero    = refl
swapCons _ _ _ _ (suc _) = refl

[]≔-++ : ∀ (xs : Vector A m) (ys : Vector A n) p v
  → (xs ++ ys) [ p ↑ˡ n ]≔ v ≗ xs [ p ]≔ v ++ ys
[]≔-++ {m = m} {n} xs ys p v i with i ≟ p ↑ˡ n
... | yes refl rewrite updateAt-updates i {const v} (xs ++ ys) | splitAt-↑ˡ m p n =
  sym (updateAt-updates p _)
... | no   i≢p rewrite updateAt-minimal _ _ {const v} (xs ++ ys) i≢p with splitAt m i in splitEq
...  | inj₁ j = sym (updateAt-minimal j p xs (λ where refl → i≢p (sym (splitAt⁻¹-↑ˡ splitEq))))
...  | inj₂ _ = refl

cong-updateAt : ∀ {xs ys : Vector A n} p f → xs ≗ ys →
  updateAt xs p f ≗ updateAt ys p f
cong-updateAt zero f xs≡ys zero = cong f (xs≡ys zero)
cong-updateAt (suc p) f xs≡ys zero = xs≡ys zero
cong-updateAt zero f xs≡ys (suc i) = xs≡ys (suc i)
cong-updateAt (suc p) f xs≡ys (suc i) = cong-updateAt p f (xs≡ys ∘ suc) i

swapV-++ : ∀ (xs : Vector A m) (ys : Vector A n) p q
  → swapV (xs ++ ys) (p ↑ˡ n) (q ↑ˡ n) ≗ swapV xs p q ++ ys
swapV-++ {m = m} {n} xs ys p q i = begin
  (xs++ysP [ q↑n ]≔ xs++ys p↑n) i ≡⟨ cong-updateAt q↑n _ xs++ysP-split i ⟩
  ((xs [ p ]≔ xs q ++ ys) [ q↑n ]≔ xs++ys p↑n) i ≡⟨ xs++ysQ-split i ⟩
  ((xs [ p ]≔ xs q ++ ys) [ q ↑ˡ n ]≔ xs p) i ≡⟨ []≔-++ (xs [ p ]≔ xs q) _ _ _ i ⟩
  (xs [ p ]≔ xs q [ q ]≔ xs p ++ ys) i ∎
  where
  xs++ys = xs ++ ys
  p↑n = p ↑ˡ n
  q↑n = q ↑ˡ n

  xs++ysP = xs++ys [ p↑n ]≔ xs++ys q↑n

  xs++≡q : xs++ys q↑n ≡ xs q
  xs++≡q = lookup-++ˡ xs ys _

  xs++≡p : xs++ys p↑n ≡ xs p
  xs++≡p = lookup-++ˡ xs ys _

  xs++ysP-split : xs++ysP ≗ xs [ p ]≔ xs q ++ ys
  xs++ysP-split i = trans ([]≔-++ xs ys _ _ i)
    (cong (λ x → (xs [ p ]≔ x ++ ys) i) xs++≡q)

  xs++ysQ-split : (xs [ p ]≔ xs q ++ ys) [ q↑n ]≔ xs++ys p↑n
    ≗ (xs [ p ]≔ xs q ++ ys) [ q↑n ]≔ xs p
  xs++ysQ-split i = cong (λ x → ((xs [ p ]≔ xs q ++ ys) [ q↑n ]≔ x) i) xs++≡p

swap-exchange : ∀ (xs : Vector A n) i j → swapV xs i j ≗ swapV xs j i
swap-exchange xs i j k with i ≟ j | k ≟ i | k ≟ j
... | yes refl | _ | _  = refl
... | no i≢j | yes refl | _ = begin
 _ ≡⟨ updateAt-minimal _ _ _ i≢j ⟩
 _ ≡⟨ updateAt-updates i _ ⟩
 _ ≡˘⟨ updateAt-updates i _ ⟩
 _ ∎
... | no i≢j | no k≢i | yes refl = begin
  _ ≡⟨ updateAt-updates j _ ⟩
  _ ≡˘⟨ updateAt-updates j _ ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ (i≢j ∘ sym) ⟩
  _ ∎
... | no i≢j | no k≢i | no k≢j = begin
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ∎

swap-injective : ∀ {xs ys : Vector A n} {i j} → swapV xs i j ≗ swapV ys i j → xs ≗ ys
swap-injective {n = n} {xs} {ys} {i} {j} same k with k ≟ i | k ≟ j | i ≟ j
... | yes refl | yes refl | _ = begin
  _ ≡˘⟨ updateAt-updates i _ ⟩
  _ ≡⟨ same k ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | yes refl | no k≢j | yes refl = begin
  _ ≡˘⟨ updateAt-updates i _ ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ same k ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | yes refl | no k≢j | no i≢j = begin
  _ ≡˘⟨ updateAt-updates j _ ⟩
  _ ≡⟨ same j ⟩
  _ ≡⟨ updateAt-updates j _ ⟩
  _ ∎
... | no k≢i | yes refl | _ = begin
  _ ≡˘⟨ updateAt-updates i _ ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ (k≢i ∘ sym) ⟩
  _ ≡⟨ same i ⟩
  _ ≡⟨ updateAt-minimal _ _ _ (k≢i ∘ sym) ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | no k≢i | no k≢j | _ = begin
  _ ≡˘⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ≡˘⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ same k ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ∎


swap-involute : ∀ (xs : Vector A n) i j → swapV (swapV xs i j) i j ≗ xs
swap-involute xs i j k with k ≟ i | k ≟ j | i ≟ j
... | yes refl | yes refl | _ = begin
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | yes refl | no k≢j | _ = begin
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ≡⟨ updateAt-updates j _ ⟩
  _ ∎
... | no k≢i | yes refl | no i≢j = begin
  _ ≡⟨ updateAt-updates j _ ⟩
  _ ≡⟨ updateAt-minimal _ _ _ i≢j ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | no k≢i | yes refl | yes refl = begin
  _ ≡⟨ updateAt-updates j _ ⟩
  _ ≡⟨ updateAt-updates i _ ⟩
  _ ∎
... | no k≢i | no k≢j | _ = begin
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ∎

swap-same-left : ∀ {xs ys : Vector A n} {i j} → swapV xs i j ≗ ys → xs ≗ swapV ys i j
swap-same-left {n = n} {xs} {ys} {i} {j} same =
  swap-injective λ j → trans (same _) (sym (swap-involute ys _ _ _))

swap-diff : ∀ (xs : Vector A n) k {i j} → k ≢ i → k ≢ j → swapV xs i j k ≡ xs k
swap-diff xs k {i} {j} k≢i k≢j = begin
  _ ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
  _ ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
  _ ∎


firstHasProperty : {A : Set ℓ} (xs : Vector A n) (f : A → Bool) →
  maybe (λ (_ , a) → T (f a)) ⊤ (findFirst xs f)
firstHasProperty {n = ℕ.zero} xs f = _
firstHasProperty {n = ℕ.suc n} xs f with f (xs zero) in eqF0
... | true rewrite eqF0 = _
... | false rewrite eqF0 with findFirst (tail xs) f in eqF | firstHasProperty (tail xs) f
... | just _ | prop = prop
... | nothing | _ rewrite eqF = _

appendLastFromℕ : ∀ (xs : Vector A n) a → appendLast xs a (fromℕ _) ≡ a
appendLastFromℕ {n = ℕ.zero} xs a = refl
appendLastFromℕ {n = ℕ.suc n} xs a = appendLastFromℕ (tail xs) a

appendLastInj : ∀ (xs : Vector A n) a i → appendLast xs a (inject₁ i) ≡ xs i
appendLastInj xs a zero = refl
appendLastInj xs a (suc i) = appendLastInj (tail xs) a i

appendLastLower : ∀ (xs : Vector A n) a i (n≢i : n ≢ toℕ i) → appendLast xs a i ≡ xs (lower₁ i n≢i)
appendLastLower {n = ℕ.zero} xs a zero n≢i = contradiction refl n≢i
appendLastLower {n = ℕ.suc n} xs a zero n≢i = refl
appendLastLower {n = ℕ.suc n} xs a (suc i) n≢i = appendLastLower (tail xs) a i (λ n≡i → n≢i (cong ℕ.suc n≡i))
