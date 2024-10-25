open import Level using (Level; _⊔_)
open import Function
open import Data.Empty
open import Data.Unit.Polymorphic
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Properties using (<⇒≤; ≤⇒≯)
open import Data.Product
open import Data.Irrelevant
open import Data.Sum
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Fin.Induction
open import Induction.WellFounded
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary hiding (Irrelevant; Recomputable)
open import Relation.Unary using (Pred; Recomputable)
open import Relation.Unary.Consequences
open import Algebra hiding (Invertible)
open import Algebra.Apartness
import Algebra.Properties.Ring as RingProps
import Algebra.Definitions as ADefs

private variable
  c ℓ ℓ₁ ℓ₂ : Level
  A B : Set ℓ
  m n : ℕ
  i j k : Fin n

i≢j→si≢sj : i ≢ j → F.suc i ≢ F.suc j
i≢j→si≢sj i≢j refl = i≢j refl

IsInj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set _
IsInj₁ (inj₁ _) = ⊤
IsInj₁ (inj₂ _) = ⊥

fromIsInj₁ : ∀ {a b} {A : Set a} {B : Set b} {a⊎b : A ⊎ B} → IsInj₁ a⊎b → A
fromIsInj₁ {a⊎b = inj₁ x} _ = x

record Σ′ (A : Set ℓ) (B : A → Set ℓ₁) : Set (ℓ ⊔ ℓ₁) where
  constructor _∙∙_
  field
    fst′′ : A
    .snd′′ : B fst′′
open Σ′ public

IsInj₂ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set _
IsInj₂ (inj₁ _) = ⊥
IsInj₂ (inj₂ _) = ⊤

fromIsInj₂ : ∀ {a b} {A : Set a} {B : Set b} {a⊎b : A ⊎ B} → IsInj₂ a⊎b → B
fromIsInj₂ {a⊎b = inj₂ x} _ = x

split : (a⊎b : A ⊎ B) → Σ′ A (λ a → inj₁ a ≡ a⊎b) ⊎ Σ′ B λ b → inj₂ b ≡ a⊎b
split (inj₁ x) = inj₁ (x ∙∙ refl)
split (inj₂ y) = inj₂ (y ∙∙ refl)

inj< : {i j : Fin n} → i F.< j → inject₁ i F.< inject₁ j
inj< {_} {zero} {suc j} (s≤s i<j) = s≤s z≤n
inj< {_} {suc i} {suc j} (s≤s i<j) = s≤s (inj< i<j)

inj<from : ∀ (i : Fin n) → inject₁ i F.< fromℕ n
inj<from zero = s≤s z≤n
inj<from (suc i) = s≤s (inj<from i)

cong≤ˡ : ∀ {i j k : ℕ} → i ℕ.≤ j → j ≡ k → i ℕ.≤ k
cong≤ˡ p refl = p

cong≤ʳ : ∀ {i j k : ℕ} → j ≡ k → i ℕ.≤ j → i ℕ.≤ k
cong≤ʳ refl p = p

cong≤ʳ₂ : ∀ {i j k : ℕ} → i ≡ j → i ℕ.≤ k → j ℕ.≤ k
cong≤ʳ₂ refl p = p

lowerMaximum : (i : Fin (suc n)) (i≢n : i ≢ fromℕ n) → Fin n
lowerMaximum {zero} zero i≢n = ⊥-elim (i≢n refl)
lowerMaximum {suc n} zero i≢n = zero
lowerMaximum {suc n} (suc i) i≢n = suc (lowerMaximum i (λ i≡n → i≢n (cong suc i≡n)))

lowerMaximumInjective : {i j : Fin (suc n)} {i≢n : i ≢ fromℕ n} {j≢n : j ≢ fromℕ n}
  → lowerMaximum i i≢n ≡ lowerMaximum j j≢n → i ≡ j
lowerMaximumInjective {zero} {zero} {zero} {i≢n} {j≢n} leqn = refl
lowerMaximumInjective {suc n} {zero} {zero} {i≢n} {j≢n} leqn = refl
lowerMaximumInjective {suc n} {suc i} {suc j} {i≢n} {j≢n} leqn =
  cong suc (lowerMaximumInjective (suc-injective leqn))

finSuc : Fin n → Fin (suc n)
finSuc zero = zero
finSuc (suc p) = suc (finSuc p)

finSuc≢fromℕ : {i : Fin n} → finSuc i ≢ fromℕ n
finSuc≢fromℕ {_} {zero} ()
finSuc≢fromℕ {_} {suc i} eqn = finSuc≢fromℕ (suc-injective eqn)

lowerMaximum≡p : {p : Fin (suc n)} (fp≢n : finSuc p ≢ F.suc (fromℕ n)) → lowerMaximum (finSuc p) fp≢n ≡ p
lowerMaximum≡p {p = zero} fp≢n = refl
lowerMaximum≡p {suc n} {p = suc p} fp≢n = cong suc (lowerMaximum≡p λ fp≡n → fp≢n (cong suc fp≡n))

isMaximum : Fin n → Set
isMaximum {suc n} = _≡ fromℕ n

isMaximum? : (p : Fin n) → Dec (isMaximum p)
isMaximum? {suc n} = F._≟ fromℕ n

maximum≥all : {i j : Fin n} → isMaximum i → i F.≥ j
maximum≥all {suc n} {zero} {zero} imax = z≤n
maximum≥all {suc zero} {zero} {suc ()} refl
maximum≥all {suc (suc n)} {zero} {suc j} ()
maximum≥all {suc n} {suc i} {zero} imax = z≤n
maximum≥all {suc (suc n)} {suc i} {suc j} imax = s≤s (maximum≥all (suc-injective imax))

_max⊎>_ : (i j : Fin n) → Set
i max⊎> j = isMaximum i × isMaximum j ⊎ i F.> j

Fin⊤ : ℕ → Set
Fin⊤ n = Fin n ⊎ ⊤

≤∧s≢⇒≤ : ∀ {m n} → m ℕ.≤ suc n → m ≢ suc n → m ℕ.≤ n
≤∧s≢⇒≤ {_} {n} z≤n q = z≤n
≤∧s≢⇒≤ {suc _} {zero} (s≤s z≤n) q = ⊥-elim (q refl)
≤∧s≢⇒≤ {suc _} {suc n} (s≤s p) q = s≤s (≤∧s≢⇒≤ p λ where refl → q refl)

i>j→i≢j : i F.> j → i ≢ inject₁ j
i>j→i≢j i>j refl = <⇒≢ (≤̄⇒inject₁< i>j) refl

i>j→i≥j : ∀ {i} {j : Fin n} → i F.≥ suc j → i F.≥ inject₁ j
i>j→i≥j = ≤-trans (<⇒≤ (≤̄⇒inject₁< ≤-refl))

i>j→i>injJ : i F.> j → i F.> inject₁ j
i>j→i>injJ = cong≤ʳ₂ (cong suc (sym (toℕ-inject₁ _)))

<→Σinject : ∀ {i j : Fin (suc n)} → i F.< j → Σ[ k ∈ Fin n ] inject₁ k ≡ i
<→Σinject {suc n} {zero} {suc j} i<j = zero , refl
<→Σinject {suc n} {i = suc i} {suc j} (s≤s i<j) =
  let (p , q) = <→Σinject {i = i} {j} i<j in
  suc p , cong suc q

punchOut-fromℕ : ∀ {i : Fin (suc n)} (n≢i : fromℕ n ≢ i) → toℕ (punchOut n≢i) ≡ toℕ i
punchOut-fromℕ {zero}  {zero } n≢i = ⊥-elim (n≢i refl)
punchOut-fromℕ {suc n} {zero } n≢i = refl
punchOut-fromℕ {suc n} {suc i} n≢i = cong suc (punchOut-fromℕ λ where refl → n≢i refl)

punchIn-fromℕ : (i : Fin n) → toℕ (punchIn (fromℕ _) i) ≡ toℕ i
punchIn-fromℕ zero = refl
punchIn-fromℕ (suc i) = cong suc (punchIn-fromℕ i)

>-weakInduction-endingFrom : ∀ (P : Pred (Fin (suc n)) ℓ) →
                               ∀ {i} → P i →
                               (∀ j → P (suc j) → P (inject₁ j)) →
                               ∀ {j} → j F.≤ i → P j
>-weakInduction-endingFrom {n} P {i} Pi Pᵢ₊₁⇒Pᵢ {j} j≤i = induct (>-wellFounded _) (F.<-cmp i j) j≤i
  where
  induct : ∀ {j} → Acc F._>_ j → Tri (i F.< j) (i ≡ j) (i F.> j) → j F.≤ i → P j
  induct (acc rs) (tri≈ _ refl _) j≤i = Pi
  induct (acc rs) (tri< i>j _ _) j≤i with () ← ≤⇒≯ j≤i i>j
  induct {j} (acc rs) (tri> _ _ i>j) _ = subst P isj≡j (Pᵢ₊₁⇒Pᵢ sj PSj)
    where

    sj×≡ : Σ[ k ∈ Fin n ] inject₁ k ≡ j
    sj×≡ = <→Σinject i>j

    sj = sj×≡ .proj₁

    isj≡j : inject₁ sj ≡ j
    isj≡j = sj×≡ .proj₂

    sj>j : suc sj F.> j
    sj>j = subst (suc sj F.>_) isj≡j (≤̄⇒inject₁< {i = sj} {j = sj} (≤-refl {x = sj}))

    sj≤i : suc sj F.≤ i
    sj≤i = subst (λ x → suc x ℕ.≤ toℕ i) (trans (sym (cong toℕ isj≡j)) (toℕ-inject₁ sj)) i>j

    PSj : P (suc sj)
    PSj = induct (rs sj>j) (F.<-cmp i (suc sj)) sj≤i

≤Rec : Recomputable (F._≤_ {_} {n} i)
≤Rec = dec⇒recomputable (F._≤?_ _)

suc-pred : n ℕ.> 0 → ℕ.suc (ℕ.pred n) ≡ n
suc-pred (s≤s {n = zero} z≤n) = refl
suc-pred (s≤s {n = suc n} z≤n) rewrite suc-pred ((s≤s {n = n} z≤n)) = refl

module hFieldProps (hField : HeytingField c ℓ₁ ℓ₂) where

  open module HF = HeytingField hField
  open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
  open CommutativeRing commutativeRing using (ring)
  open ADefs _≈_ using (Invertible)
  open ReasonSetoid HF.setoid
  open RingProps ring

  private variable
    x y : Carrier

  tightʳ : x # y → ¬ x ≈ y
  tightʳ p q = tight _ _ .proj₂ q p

  tightBoth : x # y → x ≈ y → A
  tightBoth x#y x≈y = contradiction x≈y (tightʳ x#y)

  x#0→x⁻¹*x≈1 : (x#0 : x # 0#) → #⇒invertible x#0 .proj₁ HF.* x ≈ 1#
  x#0→x⁻¹*x≈1 {x} x#0 = helper (#⇒invertible x#0)
    where
    helper : (hf@(x⁻¹ , _) : Invertible 1# HF._*_ (x HF.- 0#)) → x⁻¹ HF.* x ≈ 1#
    helper (x⁻¹ , x⁻¹*x≈1 , _) = begin
      x⁻¹ HF.* x           ≈˘⟨ *-congˡ (+-identityʳ _) ⟩
      x⁻¹ HF.* (x HF.+ 0#) ≈˘⟨ *-congˡ (+-congˡ -0#≈0#) ⟩
      x⁻¹ HF.* (x HF.- 0#)  ≈⟨ x⁻¹*x≈1 ⟩
      1# ∎
