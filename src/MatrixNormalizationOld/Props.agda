module MatrixNormalizationOld.Props where

open import Level using (Level; _⊔_) renaming (zero to lzero)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_⊔_; _^_)
open import Data.Nat.Properties hiding (<⇒≢)
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Vec
open import Data.Vec.Recursive using (_^_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

open import lbry

private variable
  m n : ℕ
  ℓ′ ℓ′′ : Level

normTwoVectors : Rel (Fin m ^ 2) lzero
normTwoVectors {m} (p , q) (r , s) =
  LookUpRelation F._<_ (r ≡ p × s ≡ q) ×
  LookUpRelation   _≡_ (r ≡ p × s max⊎> q) ×
  LookUpRelation F._>_ (r ≡ q × s ≡ p)

  where

  LookUpRelation : Rel (Fin m) ℓ′ → Set ℓ′′ → Set _
  LookUpRelation _∼_ prop = p ∼ q → prop

normalizeTwoLines : ∀ (i j : Fin n) → i ≢ j → Rel (Vec (Fin m) n) _
normalizeTwoLines {n} {m} i j i≢j xs ys =
  sameDifferent ×
  normTwoVectors (getTupleVec xs) (getTupleVec ys)
  where

  getTupleVec : Vec (Fin m) n → Fin m × Fin m
  getTupleVec xs = lookup xs i , lookup xs j

  sameDifferent : Set _
  sameDifferent = ∀ k → k ≢ i → k ≢ j → lookup xs k ≡ lookup ys k

linesBeforeINormalized : (i : Fin (suc n)) → Vec (Fin m) n → Set lzero
linesBeforeINormalized zero _ = ⊤
linesBeforeINormalized i@(suc i') xs = ∀ j → j F.≤ i' → ∀ k → k F.> j →
  lookup xs j F.< lookup xs k

allLinesNormalized : (Vec (Fin m) n) → Set lzero
allLinesNormalized xs = ∀ i j → i F.< j → lookup xs i F.< lookup xs j

linesBeforeMaximum→allLinesNorm : ∀ {n} xs → linesBeforeINormalized {n} (fromℕ n) xs
  → allLinesNormalized {n} xs
linesBeforeMaximum→allLinesNorm {suc n} xs p i j i<j = p i (≤fromℕ _) j i<j

linesNormalizedBeforeIJ : (i : Fin n) (j : Fin (suc n)) → inject₁ i F.< j
  → Vec (Fin m) n → Set lzero
linesNormalizedBeforeIJ i j i<j xs =
  linesBeforeINormalized (suc i) xs ×
  (∀ h → h F.≤ i → ∀ k → h F.< k → k F.< j → lookup xs h F.< lookup xs k)

module _ (trustMe : ∀ {ℓ} {A : Set ℓ} → A) where

  linesNormalizedBeforeIJ++ : ∀ i j (i<j : i F.< j) (xs : Vec (Fin m) n) ys
    → linesNormalizedBeforeIJ i (inject₁ j) (inj< i<j) xs
    → normalizeTwoLines i j (<⇒≢ i<j) xs ys
    → linesNormalizedBeforeIJ i (suc j) (ℕ<⇒inject₁< (m≤n⇒m≤1+n i<j)) ys
  proj₁ (linesNormalizedBeforeIJ++ i j i<j xs ys p (sameDiff , <c , >c , ≡c)) h h≤i k k>h
    rewrite sym (sameDiff h trustMe trustMe) | sym (sameDiff k trustMe trustMe) = proj₁ p h h≤i k k>h
  proj₂ (linesNormalizedBeforeIJ++ i j i<j xs ys p (sameDiff , <c , >c , ≡c)) h h≤i k i≤k k≤j
    with F.<-cmp h i | F.<-cmp (lookup xs i) (lookup xs j) | F.<-cmp k j
  ... | tri> _ _ h>i | _ | _ = ⊥-elim $ ≤⇒≯ h≤i h>i
  ... | tri< h<i h≢i _ | _ | _ rewrite sym (sameDiff h h≢i trustMe) = trustMe
  ... | tri≈ _ refl _ | tri< Xi<j _ _ | tri> ¬a ¬b k>j = ⊥-elim (≤⇒≯ (≤-pred k≤j) k>j)
  ... | tri≈ _ refl _ | tri< Xi<j _ _ | tri≈ ¬a refl ¬c
    rewrite <c Xi<j .proj₁ | <c Xi<j .proj₂ = proj₁ p i h≤i j i<j
  ... | tri≈ _ refl _ | tri< Xi<j _ _ | tri< k<j k≢j ¬c
    rewrite <c Xi<j .proj₁ | sym (sameDiff k trustMe trustMe) = proj₁ p i h≤i k i≤k
  ... | tri≈ ¬a refl ¬c | tri≈ ¬a₁ Xi≡j ¬c₁ | _ = trustMe
  ... | tri≈ ¬a refl ¬c | tri> ¬a₁ ¬b Xi>j | _ = trustMe

  linesIJ→I : ∀ i (xs : Vec (Fin m) n)
    → linesNormalizedBeforeIJ i (fromℕ _) (inj<from i) xs
    → linesBeforeINormalized (suc i) xs
  linesIJ→I i xs p j j≤i k k>j = proj₁ p j j≤i k k>j
