module MatrixNormalization.Props where

open import Level using (Level; _⊔_) renaming (zero to lzero)
open import Function
open import Data.Empty
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum
open import Data.Sum.Relation.Binary.LeftOrder hiding (⊎-<-strictTotalOrder)
open import Data.Sum.Relation.Binary.Pointwise
open import Relation.Unary.Consequences
open import Data.Bool
open import Data.Nat as ℕ hiding (_⊔_; _^_)
open import Data.Nat.Properties as ℕ hiding (<⇒≢)
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Vec
open import Data.Vec.Recursive using (_^_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Never
open import Relation.Binary.Construct.Always as Aw using (Always)
open import Relation.Nullary.Decidable

import Never as N
open import LeftOrder
open import MatrixNormalization.FinProps
open import lbry

open FinProps

private variable
  m n : ℕ
  ℓ′ ℓ′′ ℓ′′′ : Level
  C : Set ℓ′

getTupleVec : (xs : Vec C n) (i j : Fin n) → C ^ 2
getTupleVec xs i j = lookup xs i , lookup xs j

module PropNorm {c ℓ₁ ℓ₂} (rel : StrictTotalOrder c ℓ₁ ℓ₂) where
  open module A' = StrictTotalOrder rel renaming (Carrier to A')

  A-strictTotalOrder : StrictTotalOrder _ _ _
  A-strictTotalOrder = ⊎-<-strictTotalOrder {e = ℓ₂} {f = ℓ₂} rel (N.strictTotalOrder _ _)

  open module A = StrictTotalOrder A-strictTotalOrder
    renaming (Carrier to A; _<_ to _A<_) public

  _A>_ = flip _A<_

  _⊎<_ : Rel A _
  _⊎<_ = A'._<_ ⊎-< (Always {ℓ = ℓ₂})
  _⊎>_ = flip _⊎<_

  Never→Always : ∀ {p q} → p A< q → p ⊎< q
  Never→Always ₁∼₂ = ₁∼₂
  Never→Always (₁∼₁ x∼y) = ₁∼₁ x∼y

  _≈≡_ : (p q : A) → _
  _≈≡_ = Pointwise A'._≈_ _≡_

  _⊎≤_ : Rel A _
  p ⊎≤ q = (p A< q) ⊎ (p ≈≡ q)
  _⊎≥_ = flip _⊎≤_

  trans<< : ∀ {p q r} → p ⊎< q → q ⊎< r → p ⊎< r
  trans<< {p} {q} {r} = ⊎-<-transitive A'.trans (Aw.trans _ _ {p} {q} {r})

  trans≈≡< : ∀ {p q r} → p ≈≡ q → q ⊎< r → p ⊎< r
  trans≈≡< (inj₁ p≈q) ₁∼₂ = ₁∼₂
  trans≈≡< (inj₁ p≈q) (₁∼₁ q∼r) = ₁∼₁ (A'.<-respˡ-≈ (IsEquivalence.sym A'.isEquivalence p≈q) q∼r)
  trans≈≡< (inj₂ refl) q<r = q<r

  TriSet : (p q : A) → Set _
  TriSet p q = Tri (p A< q) (p ≈≡ q) (p A> q)

  normTwoVectors' : {p q : A} → TriSet p q → A ^ 2 → Set (c ⊔ ℓ₂)
  normTwoVectors' {p} {q} (tri< _ _ _) (r , s) = r ≡ p × s ≡ q
  normTwoVectors' {p} {q} (tri≈ _ _ _) (r , s) = r ≡ p × s ⊎> q
  normTwoVectors' {p} {q} (tri> _ _ _) (r , s) = r ≡ q × s ≡ p

  trichotmous-⊎-< : Trichotomous (Pointwise A'._≈_ _≡_) (A'._<_ ⊎-< (Never {ℓ′} {ℓ′′}))
  trichotmous-⊎-< = ⊎-<-trichotomous A'.compare (N.trichotomous _ _)

  normTwoVectors : Rel (A ^ 2) (c ⊔ ℓ₂)
  normTwoVectors (p , q) = normTwoVectors' (trichotmous-⊎-< p q)

  normalizeTwoLines : ∀ (i j : Fin n) → .(i ≢ j) → Rel (Vec A n) _
  normalizeTwoLines {n} i j i≢j xs ys =
    sameDifferent ×
    normTwoVectors (getTupleVec xs i j) (getTupleVec ys i j)
    where

    sameDifferent : Set _
    sameDifferent = ∀ k → k ≢ i → k ≢ j → lookup xs k ≡ lookup ys k

  linesBeforeINormalized : (i : Fin n) → Vec A n → Set (c ⊔ ℓ₂)
  linesBeforeINormalized i xs = ∀ j → j F.≤ i → ∀ k → k F.> j →
    lookup xs j ⊎< lookup xs k

  allLinesNormalized : Vec A n → Set _
  allLinesNormalized xs = ∀ i j → i F.< j → lookup xs i ⊎< lookup xs j

  allLinesNonZero : Vec A n → Set _
  allLinesNonZero xs = ∀ i → IsInj₁ (lookup xs i)

  allLinesNonZeroAndNorm : Vec A n → Set _
  allLinesNonZeroAndNorm xs = allLinesNonZero xs × allLinesNormalized xs

  linesBeforeMaximum→allLinesNorm : ∀ xs → linesBeforeINormalized {suc n} (fromℕ n) xs
    → allLinesNormalized xs
  linesBeforeMaximum→allLinesNorm xs p i j i<j = p i (≤fromℕ _) j i<j

  linesNormalizedBeforeIJ : (i j : Fin n) .(i≤j : i F.≤ j)
    → Vec A n → Set _
  linesNormalizedBeforeIJ i j i<j xs =
    (∀ h → h F.< i → ∀ k → h F.< k → lookup xs h ⊎< lookup xs k) ×
    (∀ k → i F.< k → k F.≤ j → lookup xs i ⊎< lookup xs k)

  linesNormalizedBeforeIJ++ : ∀ i j .(i≤j : i F.≤ j) (xs : Vec A (suc n)) ys
    → linesNormalizedBeforeIJ i (inject₁ j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) xs
    → normalizeTwoLines i (suc j) (<⇒≢ (s≤s i≤j)) xs ys
    → linesNormalizedBeforeIJ i (suc j) (m≤n⇒m≤1+n i≤j) ys
  proj₁ (linesNormalizedBeforeIJ++ i j i≤j xs ys (bef , after) (sameDiff , cases)) h h<i k h<k
    rewrite sym (sameDiff h (<⇒≢ h<i) (<⇒≢ (<-transˡ h<i (m≤n⇒m≤1+n (dec⟶recomputable (F._≤?_ _) i≤j)))))
    with A.compare (lookup xs i) (lookup xs (suc j)) | k F.≟ i | k F.≟ suc j
  ... | tri< a ¬b ¬c | yes refl | _ rewrite cases .proj₁ = bef _ h<i _ h<i
  ... | tri< a ¬b ¬c | no k≢i | yes refl rewrite cases .proj₂ = bef _ h<i _ h<k
  ... | tri< a ¬b ¬c | no k≢i | no k≢sj rewrite sym (sameDiff _ k≢i k≢sj) = bef h h<i k h<k
  ... | tri≈ ¬a b ¬c | yes refl | _ rewrite cases .proj₁ = bef _ h<i _ h<i
  ... | tri≈ ¬a b ¬c | no k≢i | yes refl = trans<< (bef _ h<i _ h<k) (cases .proj₂)
  ... | tri≈ ¬a b ¬c | no k≢i | no k≢sj rewrite sym (sameDiff _ k≢i k≢sj) = bef _ h<i _ h<k
  ... | tri> ¬a ¬b c | p | yes refl rewrite cases .proj₂ = bef _ h<i _ h<i
  ... | tri> ¬a ¬b c | yes refl | no k≢sj rewrite cases .proj₁ = bef _ h<k _
    (s≤s (<⇒≤ (<-transˡ h<k (dec⟶recomputable (F._≤?_ _) i≤j))))
  ... | tri> ¬a ¬b c | no k≢i | no k≢sj rewrite sym (sameDiff _ k≢i k≢sj) = bef _ h<i _ h<k
  proj₂ (linesNormalizedBeforeIJ++ i j i≤j xs ys (bef , after) (sameDiff , cases)) k i<k k≤sj
    with A.compare (lookup xs i) (lookup xs (suc j)) | k F.≟ suc j
  ... | tri< a ¬b ¬c | yes refl rewrite cases .proj₁ | cases .proj₂ = Never→Always a
  ... | tri< a ¬b ¬c | no k≢sj rewrite cases .proj₁ | sym (sameDiff _ (<⇒≢ i<k ∘ sym) k≢sj) =
    after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k≤sj λ p → k≢sj (toℕ-injective p)))
  ... | tri≈ ¬a b ¬c | yes refl rewrite cases .proj₁ = trans≈≡< b (cases .proj₂)
  ... | tri≈ ¬a b ¬c | no k≢sj rewrite cases .proj₁ | sym (sameDiff _ (<⇒≢ i<k ∘ sym) k≢sj) =
    after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k≤sj λ p → k≢sj (toℕ-injective p)))
  ... | tri> ¬a ¬b c | yes refl rewrite cases .proj₁ | cases .proj₂ = Never→Always c
  ... | tri> ¬a ¬b c | no k≢sj rewrite cases .proj₁ | sym (sameDiff _ (<⇒≢ i<k ∘ sym) k≢sj) =
    trans<< (Never→Always c)
    (after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k≤sj λ p → k≢sj (toℕ-injective p))))

  linesIJ→I : ∀ i (xs : Vec A (suc n))
    → linesNormalizedBeforeIJ i (fromℕ _) (≤fromℕ i) xs
    → linesBeforeINormalized i xs
  linesIJ→I i xs (normBef , normAfter) j j≤i k k>j with j F.≟ i
  ... | yes refl = normAfter _ k>j (≤fromℕ _)
  ... | no j≢i = normBef j (F.≤∧≢⇒< j≤i j≢i) k k>j

  norm00 : (xs : Vec A (suc n)) → linesNormalizedBeforeIJ zero zero z≤n xs
  proj₁ (norm00 xs) _ () _ _
  proj₂ (norm00 xs) zero () z≤n
  proj₂ (norm00 xs) (suc k) (s≤s _) ()

  normII : ∀ i (xs : Vec A (suc n)) → linesBeforeINormalized (inject₁ i) xs
    → linesNormalizedBeforeIJ (suc i) (suc i) F.≤-refl xs
  proj₁ (normII i xs p) h (s≤s h<si) k h<k = p _ (cong≤ʳ (sym (toℕ-inject₁ _)) h<si) _ h<k
  proj₂ (normII i xs p) k i<k k≤i = ⊥-elim (F.<-asym i<k (F.≤∧≢⇒< k≤i (<⇒≢ i<k ∘ sym)))

  finProps : FinProps (Vec A (suc n)) n
  Pij finProps = linesNormalizedBeforeIJ
  Pi finProps = linesBeforeINormalized
  P finProps = allLinesNormalized
  Pab finProps = normalizeTwoLines
  Pij→Pi finProps = linesIJ→I
  Pi→P finProps = linesBeforeMaximum→allLinesNorm
  Pi→Pii finProps = normII
  Ps finProps = linesNormalizedBeforeIJ++
  P00 finProps = norm00
