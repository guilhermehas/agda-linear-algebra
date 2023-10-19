module MatrixNormalizationOld.normLines where

open import Level using (Level; _⊔_) renaming (zero to lzero)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat as ℕ hiding (_⊔_; _^_; _*_)
open import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ hiding (_⊔_; _^_)
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Vec as V
open import Data.Vec.Recursive as VR using (_^_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import lbry
open import MatrixNormalizationOld.Props

private variable
  n : ℕ
  p px py : Fin n
  xs ys : Vec ℤ n

Lookup≢0 : (xs : Vec ℤ n) (p : Fin n) → Set
Lookup≢0 xs p = lookup xs p ≢ + 0 × ∀ i → i F.< p → lookup xs i ≡ + 0

AllZeros : (xs : Vec ℤ n) → Set
AllZeros xs = ∀ p → lookup xs p ≡ + 0

VecPivots' : (xs : Vec ℤ n) → Set
VecPivots' {n} xs = (Σ[ p ∈ Fin n ] Lookup≢0 xs p) ⊎ AllZeros xs

VecPivots'→Fin : {xs : Vec ℤ n} → VecPivots' xs → Fin (ℕ.suc n)
VecPivots'→Fin (inj₁ (p , _)) = finSuc p
VecPivots'→Fin (inj₂ _) = fromℕ _

VecPivotPos : (xs : Vec ℤ n) (p : Fin (ℕ.suc n)) → Set
VecPivotPos {zero} xs p = AllZeros xs
VecPivotPos n@{ℕ.suc _} xs p with isMaximum? p
... | yes p≡n = AllZeros xs
... | no  p≢n = Lookup≢0 xs (lowerMaximum p p≢n)

alwaysSamePivot : ∀ (xs : Vec ℤ n) p₁ p₂ → VecPivotPos xs p₁ → VecPivotPos xs p₂ → p₁ ≡ p₂
alwaysSamePivot {zero} xs zero zero vpiv₁ vpiv₂ = refl
alwaysSamePivot {suc _} xs p₁ p₂ vpiv₁ vpiv₂ with isMaximum? p₁ | isMaximum? p₂
... | yes refl | no y<Max = ⊥-elim (vpiv₂ .proj₁ (vpiv₁ (lowerMaximum p₂ y<Max)))
... | no x<Max | yes refl = ⊥-elim (vpiv₁ .proj₁ (vpiv₂ (lowerMaximum p₁ x<Max)))
... | yes refl | yes refl = refl
... | no x<Max | no y<Max with F.<-cmp (lowerMaximum p₁ x<Max) (lowerMaximum p₂ y<Max)
...   | tri< p₁<p₂ _ _ = ⊥-elim (vpiv₁ .proj₁ (vpiv₂ .proj₂ (lowerMaximum p₁ x<Max) p₁<p₂))
...   | tri> _ _ p₁>p₂ = ⊥-elim (vpiv₂ .proj₁ (proj₂ vpiv₁ (lowerMaximum p₂ y<Max) p₁>p₂))
...   | tri≈ _ p₁≡p₂ _ = lowerMaximumInjective p₁≡p₂

VecPivots : (xs : Vec ℤ n) → Set
VecPivots xs = Σ[ p ∈ _ ] VecPivotPos xs p

VecPivsTransf₁ : (vpiv : Lookup≢0 xs p) → VecPivotPos xs (finSuc p)
VecPivsTransf₁ {ℕ.suc n} {xs} {p} l≢0 with finSuc p F.≟ F.suc (fromℕ n)
... | yes eqn = ⊥-elim (finSuc≢fromℕ eqn)
... | no fp≢n rewrite lowerMaximum≡p fp≢n = l≢0

VecPivsTransf' : (vpiv : VecPivots' xs) → VecPivotPos xs (VecPivots'→Fin {xs = xs} vpiv)
VecPivsTransf' {ℕ.suc n} (inj₁ (p , l≢0)) = VecPivsTransf₁ l≢0
VecPivsTransf' {zero} (inj₂ allZ) = allZ
VecPivsTransf' {ℕ.suc n} (inj₂ allZ) with fromℕ n F.≟ fromℕ n
... | no n≢n = ⊥-elim (n≢n refl)
... | yes _ = allZ

VecPivsTransf : VecPivots' xs → VecPivots xs
VecPivsTransf vpiv = _ , VecPivsTransf' vpiv

findNonZero' : (xs : Vec ℤ n) → VecPivots' xs
findNonZero' [] = inj₂ (λ ())
findNonZero' (x ∷ xs) with x ℤ.≟ + 0 | findNonZero' xs
... | no  x≢0 | _ = inj₁ (zero , x≢0 , λ _ ())
... | yes x≡0 | inj₁ (p , lp≢0 , allZeros) = inj₁ (F.suc p , lp≢0 ,
  λ where zero i≤p → x≡0; (suc p) (s≤s i≤p) → allZeros p i≤p)
... | yes x≡0 | inj₂ allZeros = inj₂ λ where zero → x≡0 ; (suc p) → allZeros p

findNonZero : (xs : Vec ℤ n) → VecPivots xs
findNonZero = VecPivsTransf ∘ findNonZero'

findNonZeroPos : Vec ℤ n → Fin _
findNonZeroPos = proj₁ ∘ findNonZero

vecs→zeroPos : Vec ℤ n ^ 2 → Fin _ ^ 2
vecs→zeroPos = VR.map findNonZeroPos _

findNonZeroEq : VecPivotPos xs p → findNonZeroPos xs ≡ p
findNonZeroEq {xs = xs} = alwaysSamePivot _ _ _ (findNonZero xs .proj₂)

vecZeros : ∀ n → Vec ℤ n
vecZeros n = replicate (+ 0)

allZerosVecZero : AllZeros (vecZeros n)
allZerosVecZero {ℕ.suc n} zero = refl
allZerosVecZero {ℕ.suc n} (F.suc p) = allZerosVecZero p

vecZerosMax : VecPivotPos (vecZeros n) (fromℕ n)
vecZerosMax {zero} ()
vecZerosMax {ℕ.suc n} with fromℕ n F.≟ fromℕ n
... | no ¬p = ⊥-elim (¬p refl)
... | yes refl = allZerosVecZero

isMaximumReplicate : ∀ n → isMaximum (findNonZeroPos (vecZeros n))
isMaximumReplicate n = findNonZeroEq (vecZerosMax {n})

_·_ : ℤ → Vec ℤ n → Vec ℤ n
_·_ = V.map ∘ _*_

_-v_ : Vec ℤ n → Vec ℤ n → Vec ℤ n
_-v_ = zipWith ℤ._-_

module _ (trustMe : ∀ {ℓ} {A : Set ℓ} → A) where

  moreZeros≥Piv : ∀ (xs ys : Vec ℤ n)
    {px : Fin (ℕ.suc n)} {py : Fin (ℕ.suc n)} p≢max →
    (let pxx = lowerMaximum px p≢max) →
    Lookup≢0 xs pxx → VecPivotPos ys py
    → (∀ x → x F.< pxx → lookup ys x ≡ + 0)
    → lookup ys pxx ≡ + 0
    → px F.< py
  moreZeros≥Piv {zero} xs ys {zero} p≢max _ vpivys <→≡0 piv≡0 = ⊥-elim (p≢max refl)
  moreZeros≥Piv {ℕ.suc n} xs ys {px} {py} p≢max piv₁ vpivys <→≡0 piv≡0 with isMaximum? py
  ... | yes refl = trustMe
  ... | no ¬p = trustMe

  reduceVector' : (xs ys : Vec ℤ n)
    (fxs : VecPivots xs) (fys : VecPivots ys)
    (xs≡ys : fxs .proj₁ ≡ fys .proj₁)
    → Σ[ res ∈ Vec ℤ n ] (findNonZeroPos res max⊎> fys .proj₁)
  reduceVector' {zero} xs ys (zero , isPiv₁) (_ , isPiv₂) refl = [] , (inj₁ (refl , refl))
  reduceVector' n@{ℕ.suc _} xs ys (p , isPiv₁) (_ , isPiv₂) refl with p F.≟ fromℕ n
  ... | yes refl = vecZeros _ , inj₁ (isMaximumReplicate _ , refl)
  ... | no p≢max = ysn' , inj₂ (moreZeros≥Piv xs ysn' p≢max isPiv₁ (findNonZero _ .proj₂) trustMe trustMe)
    where
    pn = lowerMaximum p p≢max
    vx = lookup xs pn
    vy = lookup ys pn
    xsn = vy · xs
    ysn = vx · ys
    ysn' = ysn -v xsn

  reduceVector : (xs ys : Vec ℤ n)
    (let fxs = findNonZeroPos xs ; fys = findNonZeroPos ys)
    (xs≡ys : fxs ≡ fys)
    → Σ[ res ∈ Vec ℤ n ] (let fres = findNonZeroPos res in
      fres max⊎> fys)
  reduceVector xs ys xs≡ys = reduceVector' xs ys (findNonZero xs) (findNonZero ys) xs≡ys

  normalizeTwoLines' : (vecs : Vec ℤ n ^ 2) →
    Σ[ res ∈ Vec ℤ n ^ 2 ] normTwoVectors
    (vecs→zeroPos vecs) (vecs→zeroPos res)
  normalizeTwoLines' tp@(xs , ys) with F.<-cmp (findNonZeroPos xs) (findNonZeroPos ys)
  ... | tri< xs<ys ¬b ¬c = tp , (λ _ → refl , refl) , ⊥-elim ∘ ¬b , ⊥-elim ∘ ¬c
  ... | tri≈ ¬a xs≡ys ¬c = let vred@(zs , prop) = reduceVector xs ys xs≡ys in
    (xs , zs) , ⊥-elim ∘ ¬a , (λ x → refl , prop) , ⊥-elim ∘ ¬c
  ... | tri> ¬a ¬b xs>ys = (ys , xs) , ⊥-elim ∘ ¬a , ⊥-elim ∘ ¬b , (λ _ → refl , refl)


  module _ {ℓ} (A : Set ℓ) (m n : ℕ) (numberZeros : A → Vec (Fin m) n) where

    record FuncNorm {ℓ'} (g : Rel (Vec (Fin m) n) ℓ') : Set (ℓ ⊔ ℓ') where
      field
        f : A → A
        nZerosProp : ∀ a → g (numberZeros a) (numberZeros (f a))

    open FuncNorm

    module _ (fNormLines : ∀ i j i≢j → FuncNorm (normalizeTwoLines i j i≢j)) where
