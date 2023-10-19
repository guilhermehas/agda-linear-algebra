module MatrixNormalization.FinInductionAfter where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Nat as ℕ hiding (_⊔_; _^_)
open import Data.Nat.Properties as ℕ hiding (<⇒≢)
open import Data.Product
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Fin.Induction as F
open import Data.Vec
open import Data.Vec.Recursive using (_^_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import lbry
open import MatrixNormalization.FinProps
open import MatrixNormalization.PropsAfter

private
  open module PNorm {n} = PropNormAfter (F.<-strictTotalOrder n)

private variable
  ℓ ℓ′ ℓ′′ : Level
  m n : ℕ

record FuncNormAndZeros {ℓ} {n : ℕ} {Amn : Set ℓ}
  (numberZeros : Amn → Vec (Fin (suc n)) (suc n))
  (g : Rel (Vec (Fin (suc n)) (suc n)) ℓ′)
  (h : Vec (Fin (suc n)) (suc n) → Set ℓ′′)
  : Set (ℓ ⊔ ℓ′ ⊔ ℓ′′) where
  field
    f : ∀ a → h (numberZeros a) → Amn
    nZerosProp : (a : Amn) (ha : h (numberZeros a)) → g (numberZeros a) (numberZeros (f a ha))

record FuncNormAllLines (n : ℕ) (Amn : Set ℓ) : Set (lsuc lzero ⊔ ℓ) where

  field
    numberZeros : Amn → Vec (Fin (suc n)) (suc n)
    normProps : FinPropsInv (Vec (Fin (suc n)) (suc n)) n

  open FinPropsInv normProps

  field
    fNormLines : ∀ i j i>j → FuncNormAndZeros {n = n} {Amn}
      numberZeros (Pab i (inject₁ j) (i>j→i>injJ i>j)) (Pij i (suc j) i>j)

module _ {Amn : Set ℓ} {m n : ℕ} (fNorm : FuncNormAllLines n Amn) where

  open FuncNormAllLines fNorm
  open FuncNormAndZeros

  open FinPropsInv normProps public

  normalizeStep : ∀ (a : Amn) i j i>j
    (normBefore : Pij i (suc {n = n} j) i>j (numberZeros a))
    → Σ[ a ∈ Amn ] Pij i (inject₁ j) (i>j→i≥j i>j) (numberZeros a)
  normalizeStep a i j i>j normBefore = _ ,
    Ppred i j i>j (numberZeros a) (numberZeros (fa normBefore)) normBefore (nZerosProp fnorm a normBefore)

    where
    fnorm = fNormLines i j i>j
    fa = f fnorm a

  normalizeStepLine' : ∀ (a : Amn) i
    (normBefore : Pij i i F.≤-refl (numberZeros a))
    → Σ[ a ∈ Amn ] Pij i zero z≤n (numberZeros a)
  normalizeStepLine' a i normBefore =
    >-weakInduction-endingFrom P' Pi' PPred z≤n .proj₂

    where
    P' : Pred (Fin (suc n)) _
    P' fn = Σ[ fn≥i ∈ fn F.≤ i ] Σ[ a ∈ Amn ] Pij i fn fn≥i (numberZeros a)

    Pi' : P' i
    Pi' = F.≤-refl , _ , normBefore

    PPred : ∀ j → P' (suc j) → P' (inject₁ j)
    PPred j (sj≤i , a , normed) = i>j→i≥j sj≤i , _ , normalizeStep a _ _ sj≤i normed .proj₂

  normalizeStepLine : ∀ (a : Amn) i
    (normBefore : Pi (suc i) (numberZeros a))
    → Σ[ a ∈ Amn ] Pi (inject₁ i) (numberZeros a)
  normalizeStepLine a i normBefore =
    _ , Pij→Pi _ (numberZeros _)
    (normalizeStepLine' a (inject₁ i) (Pi→Pii _ (numberZeros _) normBefore) .proj₂)

  normalizeBeforeLast : ∀ a → Σ[ a ∈ Amn ] Pi zero (numberZeros a)
  normalizeBeforeLast a = >-weakInduction P' PLast PPred zero
    where
    P' : Pred _ _
    P' fn = Σ[ a ∈ Amn ] Pi fn (numberZeros a)

    PLast : P' (fromℕ _)
    proj₁ PLast = _
    proj₂ PLast = Pij→Pi _ (numberZeros _) (normalizeStepLine' a _ (Pnn _) .proj₂)

    PPred : ∀ i → P' (suc i) → P' (inject₁ i)
    proj₁ (PPred i Pi) = _
    proj₂ (PPred i Pi) = normalizeStepLine _ _ (Pi .proj₂) .proj₂

  normalizeA : (a : Amn) → Σ[ a ∈ Amn ] (P (numberZeros a))
  normalizeA a = _ , Pi→P (numberZeros _) (normalizeBeforeLast a .proj₂)
