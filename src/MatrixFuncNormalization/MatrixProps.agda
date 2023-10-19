open import Relation.Binary

module MatrixFuncNormalization.MatrixProps {c ℓ₁ ℓ₂} (totalOrder : StrictTotalOrder c ℓ₁ ℓ₂) where

open import Level using (Level; _⊔_; Lift; lower; lift)
open import Function
open import Data.Bool using (true; false)
open import Data.Product
open import Data.Nat using (ℕ; z≤n; s≤s; suc)
open import Data.Nat.Properties as ℕ hiding (<⇒≢; _≤?_; _≟_; ≤∧≢⇒<; <-asym; <-trans)
open import Data.Fin.Base as F using (Fin; zero; suc; inject₁; fromℕ)
open import Data.Fin.Properties hiding (≤-refl; <-trans)
open import Data.Sum as Π
open import Data.Vec.Functional
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; refl; sym)
import Relation.Binary.Construct.Add.Supremum.Strict as AddSupMod
import Relation.Binary.Construct.Add.Point.Equality as Equality
import Relation.Binary.Construct.StrictToNonStrict as StrictToNonStrict
open import Relation.Unary.Consequences
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Algebra

open import MatrixNormalization.FinProps
open import lbry

module A′ = StrictTotalOrder totalOrder
open AddSupMod A′._<_

<⁺-totalOrder : StrictTotalOrder _ _ _
<⁺-totalOrder = record { isStrictTotalOrder = <⁺-isStrictTotalOrder A′.isStrictTotalOrder }

open module STO = StrictTotalOrder <⁺-totalOrder renaming (Carrier to A) hiding (_≟_; _>_)
open module ≈ = IsEquivalence STO.isEquivalence hiding (sym)
open StrictToNonStrict _≈_ _<_ hiding (<-≤-trans)
open Equality _≈_ renaming (≈∙-refl to ≈∙-refl′)
open FinProps

_>_ = flip _<_

_<′_ : Rel A _
x <′ y = x < y ⊎ (x ≈ ⊤⁺ × y ≈ ⊤⁺)
_>′_ = flip _<′_

_≤⊤⁺ : (k : A) → k <′ ⊤⁺
k ≤⊤⁺ with compare k ⊤⁺
... | tri< k<⊤ _ _ = inj₁ k<⊤
... | tri≈ _ k≈⊤ _ = inj₂ (k≈⊤ , ≈.refl)

compare⊤⁺ = compare

private variable
  n : ℕ
  x y x′ y′ : A

<′-respʳ-≈ : _<′_ Respectsʳ _≈_
<′-respʳ-≈ y≈z (inj₁ x<y) = inj₁ (<-respʳ-≈ y≈z x<y)
<′-respʳ-≈ y≈z (inj₂ (x≈⊤ , y≈⊤)) = inj₂ (x≈⊤ , ≈.trans (≈.sym y≈z) y≈⊤)

<′-respˡ-≈ : _<′_ Respectsˡ _≈_
<′-respˡ-≈ y≈z (inj₁ x<y) = inj₁ (<-respˡ-≈ y≈z x<y)
<′-respˡ-≈ y≈z (inj₂ (x≈⊤ , y≈⊤)) = inj₂ (≈.trans (≈.sym y≈z) x≈⊤ , y≈⊤)

<′-resp-≈ : _<′_ Respects₂ _≈_
<′-resp-≈ = <′-respʳ-≈ , <′-respˡ-≈

<′-trans : Transitive _<′_
<′-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (STO.trans i<j j<k)
<′-trans (inj₁ i<j) (inj₂ (∙≈∙ , ∙≈∙)) = inj₁ i<j
<′-trans (inj₂ (∙≈∙ , ∙≈∙)) (inj₂ (∙≈∙ , ∙≈∙)) = inj₂ (Equality.∙≈∙ , Equality.∙≈∙)

LessThanRel : ∀ x′ y′ → Tri (x < y) (x ≈ y) (x > y) → Set _
LessThanRel {x} {y} x′ y′ (tri< _ _ _) = Lift (c ⊔ ℓ₂) (x′ ≈ x × y′ ≈ y)
LessThanRel {x} {y} x′ y′ (tri≈ _ _ _) = x′ ≈ x × y′ >′ y
LessThanRel {x} {y} x′ y′ (tri> _ _ _) = Lift (c ⊔ ℓ₂) (x′ ≈ y × y′ ≈ x)

NormedTwoBeforeAfter : (x y x′ y′ : A) → Set _
NormedTwoBeforeAfter x y x′ y′ = LessThanRel x′ y′ (compare x y)

NormedTwoBeforeAfter′ : ∀ {x y} x′ y′ → Tri (x < y) (x ≈ y) (x > y) → Set _
NormedTwoBeforeAfter′ {x} {y} x′ y′ tri = LessThanRel x′ y′ tri

NormedTwoBeforeAfter‵ : (i j : Fin n) → .(i ≢ j) → Rel (Vector A n) _
NormedTwoBeforeAfter‵ i j i≢j xs ys = NormedTwoBeforeAfter′ (ys i) (ys j) (compare (xs i) (xs j))

DifferentIndicesAreEqual : (i j : Fin n) → Rel (Vector A n) _
DifferentIndicesAreEqual i j xs ys = ∀ k → k ≢ i → k ≢ j → xs k ≈ ys k

BothRowsAreNormalize : (i j : Fin n) → .(i ≢ j) → Rel (Vector A n) _
BothRowsAreNormalize i j i≢j xs ys = DifferentIndicesAreEqual i j xs ys ×
  NormedTwoBeforeAfter‵ i j i≢j xs ys

BothRowsAreNormalize′ : (i j : Fin n) → .(i ≢ j) → Rel (Vector A n) _
BothRowsAreNormalize′ i j i≢j xs ys = let
  x = xs i ; y = xs j ; x′ = ys i ; y′ = ys j
  in Σ[ tri ∈ Tri (x < y) (x ≈ y) (x > y) ]
  (DifferentIndicesAreEqual i j xs ys × NormedTwoBeforeAfter′ x′ y′ tri)

RowsBeforeINormalized : (i : Fin n) → Vector A n → Set _
RowsBeforeINormalized i xs = ∀ j → j F.≤ i → ∀ k → k F.> j → xs j <′ xs k

AllRowsNormalized : Vector A n → Set _
AllRowsNormalized xs = ∀ i j → i F.< j → xs i <′ xs j

rowsBeforeMaximum→allRowsNorm : ∀ xs → RowsBeforeINormalized {suc n} (fromℕ n) xs
  → AllRowsNormalized xs
rowsBeforeMaximum→allRowsNorm xs p i j i<j = p i (≤fromℕ _) j i<j

RowsNormalizedBeforeIJ : (i j : Fin n) .(i≤j : i F.≤ j)
  → Vector A n → Set _
RowsNormalizedBeforeIJ i j i<j xs =
  (∀ h → h F.< i → ∀ k → h F.< k → xs h <′ xs k) ×
  (∀ k → i F.< k → k F.≤ j → xs i <′ xs k)

private
  ≈∙-refl : Reflexive _≈∙_
  ≈∙-refl = ≈∙-refl′ ≈.refl

rowsNormalizedBeforeIJ++′ : ∀ i j .(i≤j : i F.≤ j) (xs : Vector A (suc n)) ys
  → RowsNormalizedBeforeIJ i (inject₁ j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) xs
  → BothRowsAreNormalize′ i (suc j) (<⇒≢ (s≤s i≤j)) xs ys
  → RowsNormalizedBeforeIJ i (suc j) (m≤n⇒m≤1+n i≤j) ys
proj₁ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri< _ _ _ , sameDiff , lift (ysI≈xsI , ysJ+1≈xsJ+1))) h h<i k h<k
  with k ≟ i | k ≟ suc j
... | yes refl | _ = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (≈.sym ysI≈xsI) (bef _ h<i _ h<k))
... | no k≢i | yes refl = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i) (<⇒≢ (<-≤-trans h<i
  (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (≈.sym ysJ+1≈xsJ+1) (bef _ h<i _ h<k))
... | no k≢i | no k≢j+1 = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (sameDiff _ k≢i k≢j+1) (bef _ h<i _ h<k))
proj₁ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri≈ _ _ _ , sameDiff , ysI≈xsI , ysJ+1>xsJ+1)) h h<i k h<k
  with k ≟ i | k ≟ suc j
... | yes refl | _ = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (≈.sym ysI≈xsI) (bef _ h<i _ h<k))
... | no k≢i | yes refl = <′-trans (<′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j))))) (bef _ h<i _ h<k)) ysJ+1>xsJ+1
... | no k≢i | no k≢j+1 = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (sameDiff _ k≢i k≢j+1) (bef _ h<i _ h<k))
proj₁ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri> _ _ _ , sameDiff , lift (ysI≈xsJ+1 , ysJ+1≈xsI))) h h<i k h<k
  with k ≟ i | k ≟ suc j
... | _ | yes refl = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i) (<⇒≢
  (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (≈.sym ysJ+1≈xsI) (bef _ h<i _ h<i))
... | yes refl | no k≢j+1 = <′-respˡ-≈
  (sameDiff _ (<⇒≢ h<i) (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (≈.sym ysI≈xsJ+1)
  (bef _ h<i _ (s≤s (ℕ.<⇒≤ (<-≤-trans h<k (dec⟶recomputable (_≤?_ _) i≤j))))) )
... | no k≢i | no k≢j+1 = <′-respˡ-≈ (sameDiff _ (<⇒≢ h<i)
  (<⇒≢ (<-≤-trans h<i (m≤n⇒m≤1+n (dec⟶recomputable (_≤?_ _) i≤j)))))
  (<′-respʳ-≈ (sameDiff _ k≢i k≢j+1) (bef _ h<i _ h<k))

proj₂ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri< xsI<xsJ _ _ , sameDiff , lift (ysI≈xsI , ysJ+1≈xsJ+1))) k i<k k<sj
  with k ≟ suc j
... | yes refl = <′-respˡ-≈ (≈.sym ysI≈xsI) (<′-respʳ-≈ (≈.sym ysJ+1≈xsJ+1) (inj₁ xsI<xsJ))
... | no k≢j+1 = <′-respˡ-≈ (≈.sym ysI≈xsI) (<′-respʳ-≈ (sameDiff _ (<⇒≢ i<k ∘ sym) k≢j+1)
  (after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k<sj λ p → k≢j+1 (toℕ-injective p)))))
proj₂ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri≈ _ xsI≈xsJ _ , sameDiff , ysI≈xsI , ysJ+1>xsJ+1)) k i<k k<sj
  with k ≟ suc j
... | yes refl = <′-respˡ-≈ (≈.sym ysI≈xsI) (<′-respˡ-≈ (≈.sym xsI≈xsJ) ysJ+1>xsJ+1)
... | no k≢j+1 = <′-respˡ-≈ (≈.sym ysI≈xsI) (<′-respʳ-≈ (sameDiff _ (<⇒≢ i<k ∘ sym) k≢j+1)
  (after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k<sj λ p → k≢j+1 (toℕ-injective p)))))
proj₂ (rowsNormalizedBeforeIJ++′ i j i≤j xs ys (bef , after)
  (tri> _ _ xsI>xsJ+1 , sameDiff , lift (ysI≈xsJ+1 , ysJ+1≈xsI))) k i<k k<sj
  with k ≟ suc j
... | yes refl = <′-respˡ-≈ (≈.sym ysI≈xsJ+1) (<′-respʳ-≈ (≈.sym ysJ+1≈xsI) (inj₁ xsI>xsJ+1))
... | no k≢j+1 = <′-respˡ-≈ (≈.sym ysI≈xsJ+1) (<′-respʳ-≈ (sameDiff _ (<⇒≢ i<k ∘ sym) k≢j+1)
  (<′-trans (inj₁ xsI>xsJ+1)
  (after _ i<k (cong≤ʳ (sym (toℕ-inject₁ _)) (≤∧s≢⇒≤ k<sj λ p → k≢j+1 (toℕ-injective p))))))


rowsNormalizedBeforeIJ++ : ∀ i j .(i≤j : i F.≤ j) (xs : Vector A (suc n)) ys
  → RowsNormalizedBeforeIJ i (inject₁ j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) xs
  → BothRowsAreNormalize i (suc j) (<⇒≢ (s≤s i≤j)) xs ys
  → RowsNormalizedBeforeIJ i (suc j) (m≤n⇒m≤1+n i≤j) ys
rowsNormalizedBeforeIJ++ i j i≤j xs ys p (diff , normBef) =
  rowsNormalizedBeforeIJ++′ i j i≤j xs ys p (compare _ _ , diff , normBef)

rowsIJ→I : ∀ i (xs : Vector A (suc n))
  → RowsNormalizedBeforeIJ i (fromℕ _) (≤fromℕ i) xs
  → RowsBeforeINormalized i xs
rowsIJ→I i xs (normBef , normAfter) j j≤i k k>j with j ≟ i
... | yes refl = normAfter _ k>j (≤fromℕ _)
... | no j≢i = normBef j (≤∧≢⇒< j≤i j≢i) k k>j

norm00 : (xs : Vector A (suc n)) → RowsNormalizedBeforeIJ zero zero z≤n xs
proj₁ (norm00 xs) _ () _ _
proj₂ (norm00 xs) zero () z≤n
proj₂ (norm00 xs) (suc k) (s≤s _) ()

normII : ∀ i (xs : Vector A (suc n)) → RowsBeforeINormalized (inject₁ i) xs
  → RowsNormalizedBeforeIJ (suc i) (suc i) ≤-refl xs
proj₁ (normII i xs p) h (s≤s h<si) k h<k = p _ (cong≤ʳ (sym (toℕ-inject₁ _)) h<si) _ h<k
proj₂ (normII i xs p) k i<k k≤i = contradiction (≤∧≢⇒< k≤i (<⇒≢ i<k ∘ sym)) (<-asym i<k)

finProps : FinProps (Vector A (suc n)) n
Pij finProps = RowsNormalizedBeforeIJ
Pi finProps = RowsBeforeINormalized
P finProps = AllRowsNormalized
Pab finProps = BothRowsAreNormalize
Pij→Pi finProps = rowsIJ→I
Pi→P finProps = rowsBeforeMaximum→allRowsNorm
Pi→Pii finProps = normII
Ps finProps = rowsNormalizedBeforeIJ++
P00 finProps = norm00
