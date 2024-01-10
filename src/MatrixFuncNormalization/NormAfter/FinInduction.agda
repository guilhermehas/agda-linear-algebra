module MatrixFuncNormalization.NormAfter.FinInduction where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Function using (_$_)
open import Data.Product
open import Data.Nat as ℕ using (ℕ; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Fin
open import Data.Fin.Properties
open import Data.Fin.Induction
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import MatrixNormalization.FinProps
open import lbry

private variable
  ℓ ℓ₁ ℓ₂ : Level

record ToInduct {ℓ₁} {ℓ₂} (A : Set ℓ) (n : ℕ) : Set (lsuc $ ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f : ∀ i j i<j → A → A
    finProps : FinProps {ℓ₁ = ℓ₁} {ℓ₂} A n

  open FinProps finProps

  field
    fPab : ∀ i j i<j → (a : A) → Pab i j (<⇒≢ i<j) a (f i j i<j a)

  normalizeStep : ∀ (a : A) i j i≤j
    (normBefore : Pij i (inject₁ {n = n} j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) a)
    → Σ[ a ∈ A ] Pij i (suc j) (ℕ.<⇒≤ (s≤s i≤j)) a
  normalizeStep a i j i≤j normBefore = _ ,
    Ps i j i≤j a (f i (suc j) (ℕ.s<s i≤j) a) normBefore (fPab i (suc j) (ℕ.s<s i≤j) a)


  normalizeStepLine' : ∀ (a : A) i
    (normBefore : Pij i i ≤-refl a)
    → Σ[ a ∈ A ] Pij i (fromℕ _) (≤fromℕ _) a
  normalizeStepLine' a i normBefore =
    <-weakInduction-startingFrom P' Pi' PS (≤fromℕ i) .proj₂

    where
    P' : Pred (Fin (ℕ.suc n)) _
    P' fn = Σ[ fn≥i ∈ fn ≥ i ] Σ[ a ∈ A ] Pij i fn fn≥i a

    Pi' : P' i
    Pi' = ≤-refl , _ , normBefore

    PS : ∀ j → P' (inject₁ j) → P' (suc j)
    PS j (j≥i , a , normed) = i≤inject₁[j]⇒i≤1+j j≥i , _ , normalizeStep a _ _
      (cong≤ʳ (toℕ-inject₁ _) j≥i) normed .proj₂

  normalizeStepLine : ∀ (a : A) i
    (normBefore : Pi (inject₁ i) a)
    → Σ[ a ∈ A ] Pi (suc i) a
  normalizeStepLine a i normBefore = _ , Pij→Pi _ _ (proj₂
    (normalizeStepLine' a (suc i) (Pi→Pii _ _ normBefore)))

  getLast : A → Σ _ $ Pi (fromℕ n)
  getLast x = <-weakInduction P′ P0 PS (fromℕ _)
    where
    P′ : Pred _ _
    P′ fn = Σ[ a ∈ A ] Pi fn a

    P0 : P′ zero
    proj₁ P0 = _
    proj₂ P0 = Pij→Pi zero _ (normalizeStepLine' x _ (P00 _) .proj₂)

    PS : ∀ i → P′ (inject₁ i) → P′ (suc i)
    proj₁ (PS i Pi) = _
    proj₂ (PS i Pi) = normalizeStepLine _ _ (Pi .proj₂) .proj₂

  getProperty : A → Σ _ P
  getProperty x = _ , Pi→P _ (proj₂ (getLast x))
