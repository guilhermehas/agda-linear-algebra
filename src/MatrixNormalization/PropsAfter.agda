module MatrixNormalization.PropsAfter where

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

open import MatrixNormalization.FinProps
open import lbry
open FinPropsInv

private variable
  m n : ℕ

module PropNormAfter {c ℓ₁} (rel : StrictTotalOrder c ℓ₁ c) where
  open module A = StrictTotalOrder rel renaming (Carrier to A)
  _>A_ = flip A._<_

  AllLinesNormalizedRight : Vec A n → Set _
  AllLinesNormalizedRight xs = ∀ i j → i F.> j → lookup xs i >A lookup xs j

  LinesAfterINormalized : (i : Fin n) → Vec A n → Set _
  LinesAfterINormalized i xs = ∀ j → j F.≥ i → ∀ k → k F.< j → lookup xs k A.< lookup xs j

  NormedBeforeI : (i : Fin n) → Vec A n → Set _
  NormedBeforeI i xs = ∀ h → h F.> i → ∀ k → k F.< h → lookup xs h >A lookup xs k

  LinesNormalizedAfterIJ : (i j : Fin n) .(i≥j : i F.≥ j) → Vec A n → Set _
  LinesNormalizedAfterIJ i j i≥j xs =
    NormedBeforeI i xs ×
    (∀ k → k F.< i       → k F.≥ j → lookup xs i >A lookup xs k)

  linesIJ→I : ∀ i (xs : Vec A (suc n))
    → LinesNormalizedAfterIJ i zero z≤n xs
    → LinesAfterINormalized i xs
  linesIJ→I i xs (normAfter , normBef) j j≥i k k<j with i F.≟ j
  ... | yes refl = normBef   _ k<j z≤n
  ... | no   i≢j = normAfter _ (F.≤∧≢⇒< j≥i i≢j) _ k<j

  linesAfterMaximum→allLinesNorm : ∀ xs → LinesAfterINormalized {suc n} zero xs
    → AllLinesNormalizedRight xs
  linesAfterMaximum→allLinesNorm xs p i j i>j = p _ z≤n _ i>j

  normII : ∀ i (xs : Vec A (suc n)) → LinesAfterINormalized (suc i) xs
    → LinesNormalizedAfterIJ (inject₁ i) (inject₁ i) F.≤-refl xs
  proj₁ (normII i xs p) h h>i k h>k =
    p _ (<-transʳ (subst (toℕ i ℕ.≤_) (sym (toℕ-inject₁ _)) F.≤-refl) h>i) _ h>k
  proj₂ (normII i xs p) k i>k k≥i = ⊥-elim (≤⇒≯ k≥i i>k)

  NormalizeTwoLines : ∀ (i j : Fin n) → .(i F.> j) → Rel (Vec A n) _
  NormalizeTwoLines i j i>j xs ys = (∀ k → k ≢ j → lookup ys k ≡ lookup xs k)
    × (lookup xs i >A lookup ys j)

  LinesIJ→I : ∀ i (xs : Vec A (suc n))
    → LinesNormalizedAfterIJ i zero z≤n xs
    → LinesAfterINormalized i xs
  LinesIJ→I i xs (normAfter , normBef) j j≥i k k<j with i F.≟ j
  ... | yes refl = normBef   _ k<j z≤n
  ... | no   i≢j = normAfter _ (F.≤∧≢⇒< j≥i i≢j) _ k<j

  normNN : (xs : Vec A (suc n)) → LinesNormalizedAfterIJ (fromℕ _) (fromℕ _) F.≤-refl xs
  proj₁ (normNN xs) h h>n = ⊥-elim (≤⇒≯ (≤fromℕ _) h>n)
  proj₂ (normNN xs) k n>k k≥n = ⊥-elim (≤⇒≯ k≥n n>k)

  linesNormalizedAfterIJ++ : ∀  i (j : Fin n) .(i>j : i F.> j) xs ys →
      LinesNormalizedAfterIJ i (suc j) i>j xs →
      NormalizeTwoLines i (inject₁ j) (i>j→i>injJ i>j) xs ys →
      LinesNormalizedAfterIJ i (inject₁ j) (i>j→i≥j i>j) ys
  proj₁ (linesNormalizedAfterIJ++ i j i>j xs ys (bef , after) (sameDiff , xsi>ysj)) h h>i k h>k
    rewrite sameDiff h λ where refl → (ℕ.<⇒≢ (ℕ.<-trans (≤Rec i>j) h>i) (sym (toℕ-inject₁ _)))
    with k F.≟ inject₁ j
  ... | no k≢j rewrite sameDiff k k≢j = bef _ h>i _ h>k
  ... | yes refl = A.trans xsi>ysj (bef _ h>i _ h>i)
  proj₂ (linesNormalizedAfterIJ++ i j i>j xs ys (bef , after) (sameDiff , xsi>ysj)) k i>k k≥j
    rewrite sameDiff i (<⇒≢ (cong≤ʳ₂ (sym (cong suc (toℕ-inject₁ j))) (≤Rec i>j)) ∘ sym)
    with k F.≟ inject₁ j
  ... | no k≢j rewrite sameDiff k k≢j = after _ i>k
    (≤∧s≢⇒≤ (s≤s (cong≤ʳ₂ (toℕ-inject₁ j) k≥j)) λ sj≡sk → k≢j
      (toℕ-injective (sym (PE.trans (toℕ-inject₁ j) (cong ℕ.pred sj≡sk)))))
  ... | yes refl = xsi>ysj

  finPropsInvNewRight : FinPropsInv (Vec A (suc n)) n
  Pij finPropsInvNewRight = LinesNormalizedAfterIJ
  Pi finPropsInvNewRight = LinesAfterINormalized
  P finPropsInvNewRight = AllLinesNormalizedRight
  Pab finPropsInvNewRight = NormalizeTwoLines
  Pij→Pi finPropsInvNewRight = LinesIJ→I
  Pi→P finPropsInvNewRight = linesAfterMaximum→allLinesNorm
  Pi→Pii finPropsInvNewRight = normII
  Ppred finPropsInvNewRight = linesNormalizedAfterIJ++
  Pnn finPropsInvNewRight = normNN
