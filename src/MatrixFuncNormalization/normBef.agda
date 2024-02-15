open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.normBef {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Level hiding (suc)
open import Function
open import Data.Empty
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe)
open import Data.Maybe.Relation.Unary.Any
open import Data.Product
open import Data.Fin.Base as F hiding (lift; _-_; _+_)
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Fin.Patterns
open import Data.Sum
open import Data.Nat hiding (_⊔_; <-cmp; _≟_; _<_; _*_; _+_; _<′_)
open import Data.List using (List)
open import Data.Vec.Functional
open import Data.Vec.Functional.Properties
open import Relation.Nullary.Construct.Add.Supremum
import Relation.Binary.Construct.Add.Supremum.Strict as AddSupMod
open import Relation.Binary.PropositionalEquality as ≡ hiding (setoid; refl)
import Relation.Binary.Construct.Add.Point.Equality as Equality
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Algebra
import Algebra.Properties.Ring as RingProps

open import Algebra.Matrix.Properties
open import Algebra.Matrix.Structures
import Algebra.Module.Instances.FunctionalVector as AMIF
import MatrixFuncNormalization.MatrixProps as MatrixProps
import Algebra.Module.VecSpace as VecSpace
open import Vector.Base using (_[_]≔_)
open import MatrixFuncNormalization.FinInduction
open import Algebra.MatrixData renaming (Matrix to MatrixData)
open import lbry

open hFieldProps hField
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open MRing rawRing
open MRingProps ring
open RingProps ring
open FuncNormAllLines
open FuncNormAndZeros

open module AddSup {n} = AddSupMod (_<_ {n})
open module M = AMIF ring hiding (_+ᴹ_)
module ≈-Reasoning = ReasonSetoid setoid
open module PNorm {n} = MatrixProps (<-strictTotalOrder n)
open module PVec {n} = VecSpace (leftModule n)
open module Equality′ {a} {A} = Equality {a} {A = A} _≡_ renaming (≈∙-refl to ≈∙-refl′)

private variable
  ℓ₃ : Level
  ASet : Set ℓ₃
  m n : ℕ
  p px py : Fin n ⁺
  xs ys : Vector F n

private
  ≈∙-refl : Reflexive (_≈∙_ {A = ASet})
  ≈∙-refl = ≈∙-refl′ ≡.refl

private
  PivValue : F → Fin m ⁺ → Set ℓ₂
  PivValue x = Any $ const $ x # 0#

Lookup≢0 : (xs : Vector F n) (p : Fin n) → Set _
Lookup≢0 xs p = xs p # 0# × ∀ i → i < p → xs i ≈ 0#

AllZeros : (xs : Vector F n) → Set _
AllZeros xs = ∀ p → xs p ≈ 0#

0ⱽ : Vector F n
0ⱽ _ = 0#

VecPivots' : (xs : Vector F n) → Set _
VecPivots' xs = (Σ[ p ∈ Fin _ ] Lookup≢0 xs p) ⊎ AllZeros xs

vecPivots'→⁺ : {xs : Vector F n} → VecPivots' xs → Fin n ⁺
vecPivots'→⁺ (inj₁ (p , _)) = [ p ]
vecPivots'→⁺ (inj₂ _)       = ⊤⁺

VecPivotPos : (xs : Vector F n) (p : Fin n ⁺) → Set (ℓ₁ ⊔ ℓ₂)
VecPivotPos xs    ⊤⁺ = Lift ℓ₂ (AllZeros xs)
VecPivotPos xs [ p ] = Lookup≢0 xs p

sameVecPiv : {xs ys : Vector F n} (xs≡ys : ∀ i → xs i ≡ ys i) {p : Fin n ⁺} → VecPivotPos xs p → VecPivotPos ys p
lower (sameVecPiv xs≡ys {⊤⁺} (lift vPiv)) i rewrite ≡.sym (xs≡ys i) = vPiv i
proj₁ (sameVecPiv xs≡ys {[ p ]} (xsp#0 , ineq)) rewrite ≡.sym (xs≡ys p) = xsp#0
proj₂ (sameVecPiv xs≡ys {[ p ]} (xsp#0 , ineq)) i rewrite ≡.sym (xs≡ys i) = ineq i

alwaysSamePivot' : ∀ (xs : Vector F n) p₁ p₂ → Lookup≢0 xs p₁ → Lookup≢0 xs p₂ → p₁ ≡ p₂
alwaysSamePivot' xs p₁ p₂ (vpiv₁≢0 , vpiv₁≡0) (vpiv₂≢0 , vpiv₂≡0) with <-cmp p₁ p₂
... | tri< p₁<p₂ _ _ = ⊥-elim (tightʳ vpiv₁≢0 (vpiv₂≡0 p₁ p₁<p₂))
... | tri> _ _ p₁>p₂ = ⊥-elim (tightʳ vpiv₂≢0 (vpiv₁≡0 p₂ p₁>p₂))
... | tri≈ _ p₁≡p₂ _ = p₁≡p₂

alwaysSamePivot : ∀ (xs : Vector F n) p₁ p₂ → VecPivotPos xs p₁ → VecPivotPos xs p₂ → p₁ ≡ p₂
alwaysSamePivot xs [ x ] ⊤⁺ (xsx≢0 , _) (lift vpiv₂) = ⊥-elim (tightʳ xsx≢0 (vpiv₂ _))
alwaysSamePivot xs ⊤⁺ [ x ] (lift vpiv₁) (xsx≢0 , _) = ⊥-elim (tightʳ xsx≢0 (vpiv₁ _))
alwaysSamePivot xs ⊤⁺ ⊤⁺ vpiv₁ vpiv₂ = ≡.refl
alwaysSamePivot xs [ _ ] [ _ ] vpiv₁ vpiv₂ = cong [_] (alwaysSamePivot' xs _ _ vpiv₁ vpiv₂)

VecPiv : Vector F n → Set _
VecPiv xs = Σ[ p ∈ _ ] Lookup≢0 xs p

VecPivots : Vector F n → Set _
VecPivots xs = Σ[ p ∈ _ ] VecPivotPos xs p

VecPivotsΣ : ∀ n → Set _
VecPivotsΣ n = Σ[ xs ∈ Vector F n ] Σ[ p ∈ Fin n ⁺ ] VecPivotPos xs p

findNonZero : (xs : Vector F n) → VecPivots xs
proj₁ (findNonZero {zero} xs) = ⊤⁺
proj₂ (findNonZero {zero} xs) = lift $ λ ()
findNonZero {suc n} xs with xs F.zero ≟ 0# | findNonZero (tail xs)
... | yes xs0#0 | fn = [ F.zero ] , xs0#0 , λ _ ()
... | no xs0≈0 | [ i ] , xsI#0 , xs<I≈0 = [ suc i ] , xsI#0 ,
  λ where zero j<si → tight _ _ .proj₁ xs0≈0 ; (suc j) sj<si → xs<I≈0 j (≤-pred sj<si)
... | no xs0≈0 | ⊤⁺ , (lift allZeros) = ⊤⁺ ,
  lift (λ where zero → tight _ _ .proj₁ xs0≈0 ; (suc i) → allZeros i)

findNonZeroPos : Vector F n → Fin _ ⁺
findNonZeroPos = proj₁ ∘ findNonZero

_-v_ : Op₂ $ Vector F n
xs -v ys = xs M.+ᴹ (-ᴹ ys)

moreZeros≥Piv : ∀ {xs ys : Vector F n}
  {px : Fin n} {py : Fin n ⁺} →
  Lookup≢0 xs px → VecPivotPos ys py
  → (∀ x → x < px → ys x ≈ 0#)
  → ys px ≈ 0#
  → [ px ] <′ py
moreZeros≥Piv {py = ⊤⁺} lx vPivy ys<X≡0 ysX≡0 = _ ≤⊤⁺
moreZeros≥Piv {px = px} {[ py ]} lx (pivYs , vPivy) ys<X≡0 ysX≡0 with <-cmp px py
... | tri< px<py _ _   = inj₁ [ px<py ]
... | tri≈ _ ≡.refl  _ = tightBoth pivYs ysX≡0
... | tri> _ _ py<px   = tightBoth pivYs $ ys<X≡0 py py<px

reduceVector : ∀ {xs ys : Vector F n} {piv}
  (fxs : VecPivotPos xs piv) (fys : VecPivotPos ys piv)
  → Σ[ res ∈ Vector F n ] Σ[ pivRes ∈ Fin n ⁺ ]
    (VecPivotPos res pivRes × piv <′ pivRes × ([ xs ,, ys ] ≈ⱽ [ xs ,, res ]))
reduceVector {xs = xs} {ys} {⊤⁺} (lift fxs) (lift fys) = _ , ⊤⁺ , lift fys , (⊤⁺ ≤⊤⁺) , idR ≈ᴹ-refl
reduceVector {xs = xs} {ys}  piv@{[ pxs ]} pivXs@(fxs#0 , fxs) (_ , fys) =
  _ , helper (findNonZero ysn .proj₂)
  where
  open ≈-Reasoning

  vx = xs pxs
  vx⁻¹ = #⇒invertible fxs#0 .proj₁
  vy = ys pxs

  -vx⁻¹vy = - (vy * vx⁻¹)
  xsn = -vx⁻¹vy *ₗ xs
  ysn = ys M.+ᴹ xsn

  ysnXs<≈0 : ∀ i → i < pxs → ysn i ≈ 0#
  ysnXs<≈0 i i<pxs = begin
    ys i + -vx⁻¹vy * xs i ≈⟨ +-cong (fys i i<pxs) (*-congˡ (fxs i i<pxs)) ⟩
      0# + -vx⁻¹vy *   0# ≈⟨ +-congˡ (zeroʳ _) ⟩
      0# +             0# ≈⟨ +-identityʳ 0# ⟩
      0# ∎

  α = begin
    vy * vx⁻¹ * vx   ≈⟨ *-assoc _ _ _ ⟩
    vy * (vx⁻¹ * vx) ≈⟨ *-congˡ (x#0→x⁻¹*x≈1 fxs#0) ⟩
    vy * 1#          ≈⟨ *-identityʳ _ ⟩
    vy ∎

  vyvx⁻¹vx≈vy = begin
    - (vy * vx⁻¹) * vx ≈˘⟨ -‿distribˡ-* _ _ ⟩
    - (vy * vx⁻¹ * vx)  ≈⟨ -‿cong α ⟩
    - vy ∎

  ysnXs≈0 : ysn pxs ≈ 0#
  ysnXs≈0 = begin
    vy + - (vy * vx⁻¹) * vx ≈⟨ +-congˡ vyvx⁻¹vx≈vy  ⟩
    vy + - vy               ≈⟨ -‿inverseʳ _ ⟩
    0# ∎

  helper : ∀ {pivYs'} → VecPivotPos ysn pivYs' → Σ[ pivRes ∈ Fin _ ⁺ ]
    (VecPivotPos ysn pivRes × piv <′ pivRes × ([ xs ,, ys ] ≈ⱽ [ xs ,, ysn ]))
  helper pivYs' = _ , pivYs' , pxs≤pysn' , normed where

    pxs≤pysn' = moreZeros≥Piv pivXs pivYs' ysnXs<≈0 ysnXs≈0

    normed = rec (addCons 0F 1F (from-no (0F F.≟ 1F)) -vx⁻¹vy) (idR ≈ᴹ-refl)
      λ where 0F _ → refl ; 1F _ → refl ; (suc (suc ()))

normTwoRows : {xs ys : Vector F n} {px py : Fin n ⁺}
  (fxs : VecPivotPos xs px) (fys : VecPivotPos ys py)
  → Σ[ xs′ ∈ Vector F n ] Σ[ ys′ ∈ Vector F n ] Σ[ px′ ∈ Fin n ⁺ ] Σ[ py′ ∈ Fin n ⁺ ]
  (VecPivotPos xs′ px′ × VecPivotPos ys′ py′
  × [ xs ,, ys ] ≈ⱽ [ xs′ ,, ys′ ] × NormedTwoBeforeAfter px py px′ py′)
normTwoRows {xs = xs} {ys} {px} {py} fxs fys with compare⊤⁺ px py
... | tri< _ _ _ = xs , ys , px , py , fxs , fys , idR (λ where 0F _ → refl; (suc _) _ → refl) , lift (≈∙-refl , ≈∙-refl)
... | tri> _ _ _ = ys , xs , py , px , fys , fxs ,
  rec {ys = [ xs ,, ys ]} (swapOp 0F 1F (from-no (0F F.≟ 1F))) (idR (λ where 0F _ → refl; (suc _) _ → refl)) (λ where 0F _ → refl; 1F _ → refl) ,
    lift (≈∙-refl , ≈∙-refl)
... | tri≈ _ ∙≈∙ _ = let vecRed@(ys′ , py′ , pys′ , px<pys , vecSpacePreserverd) = reduceVector fxs fys in
  xs , ys′ , px , py′ , fxs , pys′ , vecSpacePreserverd , ≈∙-refl , px<pys
... | tri≈ _ [ ≡.refl ] _ = let vecRed@(ys′ , py′ , pys′ , px<pys , vecSpacePreserverd) = reduceVector fxs fys in
  xs , ys′ , px , py′ , fxs , pys′ , vecSpacePreserverd , ≈∙-refl , px<pys

MatrixPivots : Matrix F n m → Vector (Fin m ⁺) n → Set _
MatrixPivots xs pivsXs = ∀ i → VecPivotPos (xs i) (pivsXs i)

getMatrixPivots : (xs : Matrix F n m) → Σ[ pivs ∈ Vector (Fin m ⁺) n ] MatrixPivots xs pivs
proj₁ (getMatrixPivots xs) = _
proj₂ (getMatrixPivots xs) i = proj₂ (findNonZero (xs i))

MatrixWithPivots : (n m : ℕ) → Set _
MatrixWithPivots n m = Σ[ xs ∈ Matrix F n m ] Σ[ pivs ∈ Vector (Fin m ⁺) n ] MatrixPivots xs pivs

matrixPivs : MatrixWithPivots n m → Vector (Fin m ⁺) n
matrixPivs (_ , pivs , _) = pivs

matrix→matPivs : Matrix F n m → MatrixWithPivots n m
matrix→matPivs xs = _ , _ , getMatrixPivots xs .proj₂


normMatrixTwoRows : ∀ (xs : Matrix F n m) (pivsXs : Vector (Fin m ⁺) n)
  (mXsPivs : MatrixPivots xs pivsXs) i j i≢j →
  Σ[ ys ∈ Matrix F n m ] Σ[ pivsYs ∈ Vector (Fin m ⁺) n  ]
    (MatrixPivots ys pivsYs × xs ≈ⱽ ys × BothRowsAreNormalize i j i≢j pivsXs pivsYs)
normMatrixTwoRows {n = n@(suc ℕ.zero)} {m} xs pivsXs mXsPivs 0F 0F i≢j = contradiction ≡.refl i≢j
normMatrixTwoRows {n = n@(suc (suc _))} {m} xs pivsXs mXsPivs i j i≢j = helper (normTwoRows (mXsPivs i) (mXsPivs j))
  where

  helper : Σ[ xs′ ∈ Vector F m ] Σ[ ys′ ∈ Vector F m ] Σ[ px′ ∈ Fin m ⁺ ] Σ[ py′ ∈ Fin m ⁺ ]
    Σ[ fxs′ ∈ VecPivotPos xs′ px′ ] Σ[ fys′ ∈ VecPivotPos ys′ py′ ]
      ([ xs i ,, xs j ] ≈ⱽ [ xs′ ,, ys′ ] × NormedTwoBeforeAfter _ _ px′ py′)

    → Σ[ ys ∈ Matrix F n m ] Σ[ pivsYs ∈ Vector (Fin m ⁺) n  ]
         (MatrixPivots ys pivsYs × xs ≈ⱽ ys × BothRowsAreNormalize i j i≢j pivsXs pivsYs)
  helper (xs′ , ys′ , px′ , py′ , fxs′ , fys′ , sameVecSpace , normedBef) =
    _ , pivsYs , mPivots , sameVecSpaceAfter , differentialAreEqual , normedAfter
    where

    sameVecSpaceAfter : xs ≈ⱽ _
    sameVecSpaceAfter = stepVecSpace xs [ xs′ ,, ys′ ] i j i≢j sameVecSpace

    pivsYs : Vector (Fin m ⁺) n
    pivsYs k with does (k F.≟ i) | does (k F.≟ j)
    ... | true | _ = px′
    ... | false | true = py′
    ... | false | false = pivsXs k

    mPivots : MatrixPivots _ pivsYs
    mPivots k with k F.≟ i | k F.≟ j
    ... | yes ≡.refl | yes ≡.refl = contradiction ≡.refl i≢j
    ... | no k≢i | no k≢j = subst (λ x → VecPivotPos x (pivsXs k)) (≡.sym
      (≡.trans (updateAt-minimal _ _ _ k≢j) (updateAt-minimal _ _ _ k≢i))) (mXsPivs k)
    ... | no k≢i | yes ≡.refl = subst (λ x → VecPivotPos x py′) (≡.sym (updateAt-updates k _)) fys′
    ... | yes ≡.refl | no k≢j = subst (λ x → VecPivotPos x px′) (≡.sym
      (≡.trans (updateAt-minimal _ _ _ k≢j) (updateAt-updates i _))) fxs′

    differentialAreEqual : ∀ k → k ≢ i → k ≢ j → pivsXs k ≈∙ pivsYs k
    differentialAreEqual k k≢i k≢j rewrite dec-false (k F.≟ i) k≢i | dec-false (k F.≟ j) k≢j = ≈∙-refl

    pivsYsI≡px′ : pivsYs i ≡ px′
    pivsYsI≡px′ rewrite dec-true (i F.≟ i) ≡.refl = ≡.refl

    pivsYsJ≡py′ : pivsYs j ≡ py′
    pivsYsJ≡py′ rewrite dec-false (j F.≟ i) (i≢j ∘ ≡.sym) | dec-true (j F.≟ j) ≡.refl = ≡.refl

    normedAfter : NormedTwoBeforeAfter (pivsXs i) (pivsXs j) (pivsYs i) (pivsYs j)
    normedAfter = subst (λ x → NormedTwoBeforeAfter (pivsXs i) (pivsXs j) x (pivsYs j)) (≡.sym pivsYsI≡px′)
      (subst (NormedTwoBeforeAfter (pivsXs i) (pivsXs j) px′) (≡.sym pivsYsJ≡py′) normedBef)

funcNorm : FuncNormAllLines m n (MatrixWithPivots (suc n) m)
numberZeros funcNorm = matrixPivs
normProps funcNorm = finProps
f (fNormLines funcNorm i j i≢j) (xs , pivs , proof) = let
  ys , pivs , pivRes , _ = normMatrixTwoRows xs pivs proof i j i≢j
  in ys , pivs , pivRes
nZerosProp (fNormLines funcNorm i j i≢j) (xs , pivs , proof) = let
  ys , pivs , pivRes , vecSpace , normalized = normMatrixTwoRows xs pivs proof i j i≢j
  in normalized

usingNorm : MatrixWithPivots (suc n) m → Σ[ ys ∈ MatrixWithPivots (suc n) m ] AllRowsNormalized (matrixPivs ys)
usingNorm = normalizeA funcNorm

MatrixStart : MatrixWithPivots n m → Set _
MatrixStart xs@(xs′ , _) = Σ[ ys@(ys′ , _) ∈ MatrixWithPivots _ _ ] xs′ ≈ⱽ ys′

matrixPivsStart : (xs : MatrixWithPivots n m) → MatrixStart xs → Vector (Fin m ⁺) n
matrixPivsStart _ = matrixPivs ∘ proj₁

getMatrixStart : (xs : MatrixWithPivots n m) → MatrixStart xs
getMatrixStart xs = xs , ≈ⱽ-refl


funcNormSpaceVec : (xs : MatrixWithPivots (suc n) m) → FuncNormAllLines m n (MatrixStart xs)
numberZeros (funcNormSpaceVec xs) = matrixPivsStart xs
normProps (funcNormSpaceVec xs) = finProps
f (fNormLines (funcNormSpaceVec xs) i j i≢j) ((ys , pivs , proof) , xs≈ⱽys) = let
  (ys , pivs , pivRes , ys≈ⱽzs , _) = normMatrixTwoRows _ pivs proof i j i≢j
  in (ys , pivs , pivRes) , ≈ⱽ-trans xs≈ⱽys ys≈ⱽzs
nZerosProp (fNormLines (funcNormSpaceVec xs) i j i≢j) ((ys , pivs , proof) , xs≈ⱽys) = let
  (_ , _ , _ , _ , prop) = normMatrixTwoRows _ pivs proof i j i≢j in prop

usingNormVecSpace : (xs : MatrixWithPivots (suc n) m) (xs′ : MatrixStart xs)
  → Σ[ ys ∈ MatrixStart xs ] AllRowsNormalized (matrixPivsStart xs ys)
usingNormVecSpace = normalizeA ∘ funcNormSpaceVec

normalizeMatrix : (xs : Matrix F n m) → Σ[ (ys , pivs , _) ∈ MatrixWithPivots n m ]
  (AllRowsNormalized pivs × xs ≈ⱽ ys)
proj₁ (proj₁ (normalizeMatrix {ℕ.zero} xs)) () _
proj₁ (proj₂ (proj₁ (normalizeMatrix {ℕ.zero} xs))) ()
proj₂ (proj₂ (proj₁ (normalizeMatrix {ℕ.zero} xs))) ()
proj₁ (proj₂ (normalizeMatrix {ℕ.zero} xs)) () j x
proj₂ (proj₂ (normalizeMatrix {ℕ.zero} xs)) = idR (λ ())
normalizeMatrix {suc n} xs = let
  mPivs = matrix→matPivs xs
  res@((ys , xs≈ⱽys) , normed) = usingNormVecSpace mPivs (getMatrixStart mPivs)
  in ys , normed , xs≈ⱽys

normalizeData : Op₁ $ MatrixData F n m
normalizeData = matrixFunc→Data ∘ proj₁ ∘ proj₁ ∘ normalizeMatrix ∘ matrixData→Fun

getCoeff : MatrixData F n m → List _
getCoeff xs = let
  xsFunc = matrixData→Fun xs
  res@(_ , _ , xs≈ⱽys) = normalizeMatrix xsFunc
  in ≈ⱽ⇒listVops xs≈ⱽys
