-- This is a file to normalize a matrix of integers
module MatrixNormalization.normLinesInteger where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Empty
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Sum.Relation.Binary.LeftOrder
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Bool using (false; true)
open import Data.Nat as ℕ hiding (_⊔_; _^_; _*_)
open import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ hiding (_⊔_; _^_)
open import Data.Integer.Properties as ℤ
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Vec as V
open import Data.Vec.Properties as V
open import Data.Vec.Recursive as VR using (_^_)
open import Relation.Binary
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Algebra

open import lbry
open import MatrixNormalization.Props
open import MatrixNormalization.FinInduction

open ≡-Reasoning
open FuncNormAndZeros
open FuncNormAllLines
open module PNorm {n} = PropNorm (F.<-strictTotalOrder n)

private variable
  ℓ : Level
  C : Set ℓ
  xc yc : C
  m n : ℕ

Lookup≢0 : (xs : Vec ℤ n) (p : Fin n) → Set
Lookup≢0 xs p = lookup xs p ≢ + 0 × ∀ i → i F.< p → lookup xs i ≡ + 0

AllZeros : (xs : Vec ℤ n) → Set
AllZeros xs = ∀ p → lookup xs p ≡ + 0

VecPivots' : (xs : Vec ℤ n) → Set
VecPivots' {n} xs = (Σ[ p ∈ Fin n ] Lookup≢0 xs p) ⊎ AllZeros xs

VecPivots'→Fin : {xs : Vec ℤ n} → VecPivots' xs → Fin (ℕ.suc n)
VecPivots'→Fin (inj₁ (p , _)) = finSuc p
VecPivots'→Fin (inj₂ _) = fromℕ _

private variable
  p px py : Fin⊤ n
  xs ys : Vec ℤ n

VecPivotPos : (xs : Vec ℤ n) (p : Fin⊤ n) → Set
VecPivotPos xs (inj₂ _) = AllZeros xs
VecPivotPos xs (inj₁ p) = Lookup≢0 xs p

alwaysSamePivot' : ∀ (xs : Vec ℤ n) p₁ p₂ → Lookup≢0 xs p₁ → Lookup≢0 xs p₂ → p₁ ≡ p₂
alwaysSamePivot' xs p₁ p₂ (vpiv₁≢0 , vpiv₁≡0) (vpiv₂≢0 , vpiv₂≡0) with F.<-cmp p₁ p₂
... | tri< p₁<p₂ _ _ = ⊥-elim (vpiv₁≢0 (vpiv₂≡0 p₁ p₁<p₂))
... | tri> _ _ p₁>p₂ = ⊥-elim (vpiv₂≢0 (vpiv₁≡0 p₂ p₁>p₂))
... | tri≈ _ p₁≡p₂ _ = p₁≡p₂

alwaysSamePivot : ∀ (xs : Vec ℤ n) p₁ p₂ → VecPivotPos xs p₁ → VecPivotPos xs p₂ → p₁ ≡ p₂
alwaysSamePivot xs (inj₁ _) (inj₂ _) (xsx≢0 , _) vpiv₂ = ⊥-elim (xsx≢0 (vpiv₂ _))
alwaysSamePivot xs (inj₂ _) (inj₁ _) vpiv₁ (xsx≢0 , _) = ⊥-elim (xsx≢0 (vpiv₁ _))
alwaysSamePivot xs (inj₂ _) (inj₂ _) vpiv₁ vpiv₂ = refl
alwaysSamePivot xs (inj₁ p₁) (inj₁ p₂) vpiv₁ vpiv₂ = cong inj₁ (alwaysSamePivot' xs _ _ vpiv₁ vpiv₂)

VecPivots : (xs : Vec ℤ n) → Set
VecPivots xs = Σ[ p ∈ _ ] VecPivotPos xs p

findNonZero : (xs : Vec ℤ n) → VecPivots xs
findNonZero [] = inj₂ _ , (λ ())
findNonZero (x ∷ xs) with x ℤ.≟ + 0 | findNonZero xs
... | no  x≢0 | _ = inj₁ zero , x≢0 , λ _ ()
... | yes x≡0 | inj₂ _ , allZ = (inj₂ _) , (λ where zero → x≡0; (F.suc _) → allZ _)
... | yes x≡0 | inj₁ x , xsx≢0 , founded = inj₁ (F.suc x) , xsx≢0 ,
  (λ where zero _ → x≡0; (F.suc _) (s≤s i<x) → founded _ i<x)

findNonZeroPos : Vec ℤ n → Fin⊤ _
findNonZeroPos = proj₁ ∘ findNonZero

vecs→zeroPos : Vec ℤ n ^ 2 → Fin⊤ _ ^ 2
vecs→zeroPos = VR.map findNonZeroPos _

findNonZeroEq : VecPivotPos xs p → findNonZeroPos xs ≡ p
findNonZeroEq {xs = xs} = alwaysSamePivot _ _ _ (findNonZero xs .proj₂)

vecZeros : ∀ n → Vec ℤ n
vecZeros n = replicate _ (+ 0)

allZerosVecZero : AllZeros (vecZeros n)
allZerosVecZero {ℕ.suc n} zero = refl
allZerosVecZero {ℕ.suc n} (F.suc p) = allZerosVecZero p

vecZerosMax : VecPivotPos (vecZeros n) (inj₂ _)
vecZerosMax zero = refl
vecZerosMax (F.suc xs) = vecZerosMax xs

vecZero≡inj : findNonZeroPos (vecZeros n) ≡ inj₂ _
vecZero≡inj = findNonZeroEq {xs = vecZeros _} allZerosVecZero


_·_ : ℤ → Op₁ $ Vec ℤ n
_·_ = V.map ∘ _*_

_-v_ : Op₂ $ Vec ℤ n
_-v_ = zipWith ℤ._-_

moreZeros≥Piv : ∀ (xs ys : Vec ℤ n)
  {px : Fin n} {py : Fin⊤ n} →
  Lookup≢0 xs px → VecPivotPos ys py
  → (∀ x → x F.< px → lookup ys x ≡ + 0)
  → lookup ys px ≡ + 0
  → inj₁ px ⊎< py
moreZeros≥Piv xs ys {px} {inj₂ _} lx vPivy ys<X≡0 ysX≡0 = ₁∼₂
moreZeros≥Piv xs ys {px} {inj₁ py} lx (pivYs , vPivy) ys<X≡0 ysX≡0 with F.<-cmp px py
... | tri< a ¬b ¬c = ₁∼₁ a
... | tri≈ ¬a refl ¬c = ⊥-elim (pivYs ysX≡0)
... | tri> ¬a ¬b c = ⊥-elim (pivYs (ys<X≡0 py c))

reduceVector' : (xs ys : Vec ℤ n)
  (fxs : VecPivots xs) (fys : VecPivots ys)
  (xs≡ys : fxs .proj₁ ≡ fys .proj₁)
  → Σ[ res ∈ Vec ℤ n ] (findNonZeroPos res ⊎> fys .proj₁)
proj₁ (reduceVector' xs ys (inj₂ _ , snd) (inj₂ _ , snd₁) xs≡ys) = vecZeros _
proj₂ (reduceVector' {n} xs ys (inj₂ _ , snd) (inj₂ _ , snd₁) xs≡ys)
  rewrite vecZero≡inj {n} = ₂∼₂ _
reduceVector' xs ys (inj₁ pxs , pivXs) (inj₁ pys , pivYs) refl =
  ysn' , moreZeros≥Piv xs ysn' pivXs (findNonZero _ .proj₂) ysnXs<≡0 ysnXs≡0
  where
  vx = lookup xs pxs
  vy = lookup ys pxs
  xsn = vy · xs
  ysn = vx · ys
  ysn' = ysn -v xsn

  ysnXs<≡0 : ∀ i → i F.< pxs → lookup ysn' i ≡ +0
  ysnXs<≡0 i i<pxs = begin
    lookup ysn' i ≡⟨ lookup-zipWith ℤ._-_ i ysn xsn ⟩
    lookup ysn i ℤ.- lookup xsn i ≡⟨ cong₂ ℤ._-_
      (lookup-map i (vx *_) ys)
      (lookup-map i (vy *_) xs) ⟩
    vx * lookup ys i ℤ.- vy * lookup xs i ≡⟨ cong₂ (λ a b → vx * a ℤ.- vy * b)
      (proj₂ pivYs i i<pxs) (proj₂ pivXs i i<pxs) ⟩
    vx * + 0 ℤ.- vy * + 0 ≡⟨ cong₂ ℤ._-_ (ℤ.*-zeroʳ vx) (ℤ.*-zeroʳ vy) ⟩
    + 0 ℤ.- + 0 ≡⟨ +-inverseʳ (+ 0) ⟩
    + 0 ∎

  ysnXs≡0 : lookup ysn' pxs ≡ +0
  ysnXs≡0 = begin
    lookup ysn' pxs ≡⟨ lookup-zipWith ℤ._-_ pxs ysn xsn ⟩
    lookup ysn pxs ℤ.- lookup xsn pxs ≡⟨ cong₂ ℤ._-_
      (lookup-map pxs (vx *_) ys)
      (lookup-map pxs (vy *_) xs) ⟩
    vx * vy ℤ.- vy * vx ≡⟨ cong (λ w → vx * vy ℤ.- w) (ℤ.*-comm vy _) ⟩
    vx * vy ℤ.- vx * vy ≡⟨ +-inverseʳ (vx * vy) ⟩
    + 0 ∎

reduceVector : (xs ys : Vec ℤ n)
  (let fxs = findNonZeroPos xs ; fys = findNonZeroPos ys)
  (xs≡ys : fxs ≡ fys)
  → Σ[ res ∈ Vec ℤ n ] (let fres = findNonZeroPos res in
    fres ⊎> fys)
reduceVector xs ys xs≡ys = reduceVector' xs ys (findNonZero xs) (findNonZero ys) xs≡ys

normalizeTwoLines' : (vecs : Vec ℤ n ^ 2) →
  Σ[ res ∈ Vec ℤ n ^ 2 ] normTwoVectors
    (vecs→zeroPos vecs) (vecs→zeroPos res)
normalizeTwoLines' tp@(xs , ys) with A.compare (findNonZeroPos xs) (findNonZeroPos ys)
... | tri< _ _ _ = tp , refl , refl
... | tri> _ _ _ = (ys , xs) , refl , refl
... | tri≈ _ xs≡ys _ = let vred@(zs , prop) = reduceVector xs ys (Pointwise-≡⇒≡ xs≡ys) in
  (xs , zs) , refl , prop

Matrix : ℕ → ℕ → Set _
Matrix m n = Vec (Vec ℤ m) n

matrixZeros : Matrix m n → Vec (Fin⊤ m) n
matrixZeros = V.map findNonZeroPos

normMatrix : ∀ (xs : Matrix m n) i j i≢j →
  Σ[ ys ∈ Matrix m n ] normalizeTwoLines i j i≢j (matrixZeros xs) (matrixZeros ys)
normMatrix {m} {n} xs i j i≢j = yss , lookupXs≢Ys , normVec
  where
  xsi = lookup xs i
  xsj = lookup xs j

  yst' = normalizeTwoLines' (xsi , xsj)
  ysProp = yst' .proj₂
  yst = yst' .proj₁
  ysi = yst .proj₁
  ysj = yst .proj₂

  yss = (xs [ i ]≔ ysi) [ j ]≔ ysj

  lookupXs≢Ys : ∀ k → k ≢ i → k ≢ j → lookup (matrixZeros xs) k ≡ lookup (matrixZeros yss) k
  lookupXs≢Ys k k≢i k≢j = begin
    lookup (matrixZeros xs) k     ≡⟨  lookup-map k findNonZeroPos xs  ⟩
    findNonZeroPos (lookup xs k)  ≡˘⟨ cong findNonZeroPos helper      ⟩
    findNonZeroPos (lookup yss k) ≡˘⟨ lookup-map k findNonZeroPos yss ⟩
    lookup (matrixZeros yss) k    ∎ where

    helper = lookup yss k             ≡⟨ lookup∘update′ k≢j (xs [ i ]≔ ysi) _ ⟩
             lookup (xs [ i ]≔ ysi) k ≡⟨ lookup∘update′ k≢i xs _ ⟩
             lookup xs k              ∎

  sameNormTwoVectors : ∀ {p q r s} → p ≡ q → r ≡ s → normTwoVectors {m} p r → normTwoVectors q s
  sameNormTwoVectors refl refl ntv = ntv

  normVec : normTwoVectors _ _
  normVec = sameNormTwoVectors (×-≡,≡→≡ ((projSame _) , (projSame _))) (×-≡,≡→≡ (sym α , sym β)) ysProp
    where

    projSame : ∀ i → findNonZeroPos (lookup xs i) ≡ lookup (V.map findNonZeroPos xs) i
    projSame i = sym (lookup-map i findNonZeroPos xs)

    lookupYssI≡ysi = lookup yss i             ≡⟨ lookup∘update′ i≢j (xs [ i ]≔ ysi) _ ⟩
                     lookup (xs [ i ]≔ ysi) i ≡⟨ lookup∘update i xs _    ⟩
                     ysi ∎

    α = lookup (V.map findNonZeroPos yss) i ≡⟨ lookup-map i findNonZeroPos yss ⟩
        findNonZeroPos (lookup yss i)       ≡⟨ cong findNonZeroPos lookupYssI≡ysi ⟩
        findNonZeroPos ysi ∎

    β = lookup (matrixZeros yss) j    ≡⟨ lookup-map j findNonZeroPos yss ⟩
        findNonZeroPos (lookup yss j) ≡⟨ cong findNonZeroPos (lookup∘update j (xs [ i ]≔ ysi) _) ⟩
        findNonZeroPos ysj            ∎
