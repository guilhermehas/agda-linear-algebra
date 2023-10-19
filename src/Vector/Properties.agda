module Vector.Properties where

open import Level using (Level)
open import Function
open import Data.Sum
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
