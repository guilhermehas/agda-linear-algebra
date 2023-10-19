module MatrixFuncNormalization.FinInduction where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Properties as ℕ hiding (<⇒≢)
open import Data.Product
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Fin.Induction as F
open import Data.Vec.Functional
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Nullary.Construct.Add.Supremum

open import lbry
open import MatrixNormalization.FinProps
import MatrixFuncNormalization.MatrixProps as PropNorm

private
  open module PNorm {n} = PropNorm (F.<-strictTotalOrder n)

private variable
  ℓ ℓ′ : Level
  m n : ℕ

record FuncNormAndZeros {ℓ} {m n : ℕ} {Amn : Set ℓ}
  (numberZeros : Amn → Vector (Fin m ⁺) (suc n))
  (_≈_ : Rel (Vector (Fin m ⁺) (suc n)) ℓ′)
  : Set (ℓ ⊔ ℓ′) where
  field
    f : Amn → Amn
    nZerosProp : (a : Amn) → numberZeros a ≈ numberZeros (f a)

record FuncNormAllLines (m n : ℕ) (Amn : Set ℓ) : Set (lsuc lzero ⊔ ℓ) where

  field
    numberZeros : Amn → Vector (Fin m ⁺) (suc n)
    normProps : FinProps {ℓ₁ = lzero} (Vector (Fin m ⁺) (suc n)) n

  open FinProps normProps

  field
    fNormLines : ∀ i j i≢j → FuncNormAndZeros {m = m} {n} {Amn} numberZeros (Pab i j i≢j)

module _ {Amn : Set ℓ} {m n : ℕ} (fNorm : FuncNormAllLines m n Amn) where

  open FuncNormAllLines fNorm
  open FuncNormAndZeros

  open FinProps normProps public

  normalizeStep : ∀ (a : Amn) i j i≤j
    (normBefore : Pij i (inject₁ {n = n} j) (cong≤ʳ (sym (toℕ-inject₁ _)) i≤j) (numberZeros a))
    → Σ[ a ∈ Amn ] Pij i (suc j) (<⇒≤ (s≤s i≤j)) (numberZeros a)
  normalizeStep a i j i≤j normBefore = _ ,
    Ps i j i≤j (numberZeros a) (numberZeros fa) normBefore (nZerosProp fnorm a)

    where
    fnorm = fNormLines i (suc j) (<⇒≢ (s≤s i≤j))
    fa = f fnorm a

  normalizeStepLine' : ∀ (a : Amn) i
    (normBefore : Pij i i F.≤-refl (numberZeros a))
    → Σ[ a ∈ Amn ] Pij i (fromℕ _) (≤fromℕ _) (numberZeros a)
  normalizeStepLine' a i normBefore =
    <-weakInduction-startingFrom P' Pi' PS (≤fromℕ i) .proj₂

    where
    P' : Pred (Fin (suc n)) _
    P' fn = Σ[ fn≥i ∈ fn F.≥ i ] Σ[ a ∈ Amn ] Pij i fn fn≥i (numberZeros a)

    Pi' : P' i
    Pi' = F.≤-refl , _ , normBefore

    PS : ∀ j → P' (inject₁ j) → P' (suc j)
    PS j (j≥i , a , normed) = i≤inject₁[j]⇒i≤1+j j≥i , _ , normalizeStep a _ _
      (cong≤ʳ (toℕ-inject₁ _) j≥i) normed .proj₂

  normalizeStepLine : ∀ (a : Amn) i
    (normBefore : Pi (inject₁ i) (numberZeros a))
    → Σ[ a ∈ Amn ] Pi (suc i) (numberZeros a)
  normalizeStepLine a i normBefore =
    _ , Pij→Pi _ (numberZeros _)
    (normalizeStepLine' a (suc i) (Pi→Pii _ (numberZeros _) normBefore) .proj₂)

  normalizeBeforeLast : Amn → Σ[ a ∈ Amn ] Pi (fromℕ n) (numberZeros a)
  normalizeBeforeLast a = <-weakInduction P' P0 PS (fromℕ _)
    where
    P' : Pred _ _
    P' fn = Σ[ a ∈ Amn ] Pi fn (numberZeros a)

    P0 : P' zero
    proj₁ P0 = _
    proj₂ P0 = Pij→Pi zero (numberZeros _) (normalizeStepLine' a _ (P00 _) .proj₂)

    PS : ∀ i → P' (inject₁ i) → P' (suc i)
    proj₁ (PS i Pi) = _
    proj₂ (PS i Pi) = normalizeStepLine _ _ (Pi .proj₂) .proj₂

  normalizeA : Amn → Σ[ a ∈ Amn ] (P (numberZeros a))
  normalizeA a = _ , Pi→P (numberZeros _) (normalizeBeforeLast a .proj₂)
