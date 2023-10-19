-- This is a file to normalize a matrix composed by a field
-- it also proved that normalized matrix has the same vector space of the original one

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Empty
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Sum.Properties
open import Data.Sum.Relation.Binary.LeftOrder
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Bool using (false; true)
open import Data.Nat as ℕ hiding (_⊔_; _^_; _*_)
open import Data.Fin as F hiding (_-_)
open import Data.Fin.Properties as F
open import Data.Vec.Functional as VF
open import Data.Vec as V
open import Data.Vec.Properties as V
open import Data.Vec.Recursive as VR using (_^_)
open import Relation.Binary
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ hiding (setoid)
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary.Properties
open import Algebra
open import Algebra.Module
open import Algebra.Apartness
import Algebra.Properties.Ring as PropRing
open import Relation.Unary hiding (Decidable)

open import lbry
open import MatrixNormalization.Props
open import MatrixNormalization.FinInduction
import Algebra.Module.Instances.FunctionalVector as AMIF
import Algebra.SubModule as ASubMod
import Algebra.SubModule.Vec as ASubModVec
import Algebra.SubModule.Field as ASubModField

open FuncNormAndZeros
open FuncNormAllLines
open module PNorm {n} = PropNorm (F.<-strictTotalOrder n) hiding (_≈_)

module MatrixNormalization.normLinesField {c}
  (field' : HeytingField c c c)
  (let open HeytingField field' renaming (Carrier to F; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans))
  (_≟_ : Decidable _#_)
  (open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing))
  (open CommutativeRing commutativeRing using (ring))
  (open AMIF ring using (leftModule; _≈ᴹ_))
  (≈→∈ : ∀ {n x y} {VS : ASubMod.Cᴹ (leftModule n) c} → x ≈ᴹ y → x ∈ VS → y ∈ VS)
  where

open module ASM {n} = ASubMod (leftModule n)
open module ASMV {n} = ASubModVec (leftModule n) ≈→∈
open module ASMF {n} = ASubModField {ℓm = c} field' (leftModule n)
open PropRing ring
open module LF {n} = LeftModule (leftModule n)
open hFieldProps field'

private variable
  m n : ℕ

Lookup≢0 : (xs : Vector F n) (p : Fin n) → Set _
Lookup≢0 xs p = xs p # 0# × ∀ i → i F.< p → xs i ≈ 0#

AllZeros : (xs : Vector F n) → Set _
AllZeros {n} xs = ∀ (p : Fin n) → xs p ≈ 0#

VecPivots' : (xs : Vector F n) → Set _
VecPivots' {n} xs = (Σ[ p ∈ Fin n ] Lookup≢0 xs p) ⊎ AllZeros xs

VecPivots'→Fin : {xs : Vector F n} → VecPivots' xs → Fin (ℕ.suc n)
VecPivots'→Fin (inj₁ (p , _)) = finSuc p
VecPivots'→Fin (inj₂ _) = fromℕ _

private variable
  p px py : Fin⊤ n
  xs ys : Vector F n

VecPivotPos : (xs : Vector F n) (p : Fin⊤ n) → Set c
VecPivotPos xs (inj₂ _) = AllZeros xs
VecPivotPos xs (inj₁ p) = Lookup≢0 xs p

alwaysSamePivot' : ∀ (xs : Vector F n) p₁ p₂ → Lookup≢0 xs p₁ → Lookup≢0 xs p₂ → p₁ ≡ p₂
alwaysSamePivot' xs p₁ p₂ (vpiv₁≢0 , vpiv₁≡0) (vpiv₂≢0 , vpiv₂≡0) with F.<-cmp p₁ p₂
... | tri< p₁<p₂ _ _ = ⊥-elim (tightʳ vpiv₁≢0 (vpiv₂≡0 p₁ p₁<p₂))
... | tri> _ _ p₁>p₂ = ⊥-elim (tightʳ vpiv₂≢0 (vpiv₁≡0 p₂ p₁>p₂))
... | tri≈ _ p₁≡p₂ _ = p₁≡p₂

alwaysSamePivot : ∀ (xs : Vector F n) p₁ p₂ → VecPivotPos xs p₁ → VecPivotPos xs p₂ → p₁ ≡ p₂
alwaysSamePivot xs (inj₁ _) (inj₂ _) (xsx≢0 , _) vpiv₂ = ⊥-elim (tightʳ xsx≢0 (vpiv₂ _))
alwaysSamePivot xs (inj₂ _) (inj₁ _) vpiv₁ (xsx≢0 , _) = ⊥-elim (tightʳ xsx≢0 (vpiv₁ _))
alwaysSamePivot xs (inj₂ _) (inj₂ _) vpiv₁ vpiv₂ = refl
alwaysSamePivot xs (inj₁ p₁) (inj₁ p₂) vpiv₁ vpiv₂ = cong inj₁ (alwaysSamePivot' xs _ _ vpiv₁ vpiv₂)

VecPiv : Vector F n → Set _
VecPiv xs = Σ[ p ∈ _ ] Lookup≢0 xs p

VecPivots : Vector F n → Set _
VecPivots xs = Σ[ p ∈ _ ] VecPivotPos xs p

findNonZero : (xs : Vector F n) → VecPivots xs
proj₁ (findNonZero {zero} xs) = inj₂ _
proj₂ (findNonZero {zero} xs) ()
findNonZero {suc n} xs with xs F.zero ≟ 0# | findNonZero (VF.tail xs)
... | yes xs0#0 | fn = (inj₁ F.zero) , xs0#0 , λ _ ()
... | no xs0≈0 | inj₁ i , xsI#0 , xs<I≈0 = inj₁ (suc i) , xsI#0 ,
  λ where zero j<si → tight _ _ .proj₁ xs0≈0 ; (suc j) sj<si → xs<I≈0 j (≤-pred sj<si)
... | no xs0≈0 | inj₂ _ , allZeros = inj₂ _ ,
  λ where zero → tight _ _ .proj₁ xs0≈0 ; (suc i) → allZeros i

findNonZeroPos : Vector F n → Fin⊤ _
findNonZeroPos = proj₁ ∘ findNonZero

vecs→zeroPos : Vector F n ^ 2 → Fin⊤ _ ^ 2
vecs→zeroPos = VR.map findNonZeroPos _

findNonZeroEq : VecPivotPos xs p → findNonZeroPos xs ≡ p
findNonZeroEq {xs = xs} = alwaysSamePivot _ _ _ (findNonZero xs .proj₂)

findXs≡inj₁→L≢0 : ∀ {p : Fin n} → findNonZeroPos xs ≡ inj₁ p → Lookup≢0 xs p
findXs≡inj₁→L≢0 {xs = xs} eqn with findNonZero xs
... | inj₁ j , fNonZero = subst (Lookup≢0 xs) (inj₁-injective eqn) fNonZero

vecZeros : ∀ n → Vector F n
vecZeros n = 0ᴹ

allZerosVecZero : AllZeros (vecZeros n)
allZerosVecZero {ℕ.suc n} zero = ≈-refl
allZerosVecZero {ℕ.suc n} (F.suc p) = allZerosVecZero p

vecZerosMax : VecPivotPos (vecZeros n) (inj₂ _)
vecZerosMax zero = ≈-refl
vecZerosMax (F.suc xs) = vecZerosMax xs

vecZero≡inj : findNonZeroPos (vecZeros n) ≡ inj₂ _
vecZero≡inj = findNonZeroEq {xs = vecZeros _} allZerosVecZero

_-v_ : Op₂ $ Vector F n
xs -v ys = xs +ᴹ (-ᴹ ys)

moreZeros≥Piv : ∀ (xs ys : Vector F n)
  {px : Fin n} {py : Fin⊤ n} →
  Lookup≢0 xs px → VecPivotPos ys py
  → (∀ x → x F.< px → ys x ≈ 0#)
  → ys px ≈ 0#
  → inj₁ px ⊎< py
moreZeros≥Piv xs ys {px} {inj₂ _} lx vPivy ys<X≡0 ysX≡0 = ₁∼₂
moreZeros≥Piv xs ys {px} {inj₁ py} lx (pivYs , vPivy) ys<X≡0 ysX≡0 with F.<-cmp px py
... | tri< a ¬b ¬c = ₁∼₁ a
... | tri≈ ¬a refl ¬c = ⊥-elim (tightʳ pivYs ysX≡0)
... | tri> ¬a ¬b c = ⊥-elim (tightʳ pivYs (ys<X≡0 py c))

reduceVector' : (xs ys : Vector F n)
  (fxs : VecPivots xs) (fys : VecPivots ys)
  (xs≡ys : fxs .proj₁ ≡ fys .proj₁)
  → Σ[ res ∈ Vector F n ] (((span xs +ₛ span ys) ≅ (span xs +ₛ span res)) × findNonZeroPos res ⊎> fys .proj₁)
proj₁ (reduceVector' _ _ (inj₂ _ , _) (inj₂ _ , _) _) = vecZeros _
proj₁ (proj₂ (reduceVector' _ _ (inj₂ _ , _) (inj₂ _ , all0ys) refl)) = +ₛ-congˡ (cong-span all0ys)
proj₂ (proj₂ (reduceVector' {n} _ _ (inj₂ _ , pivXs) (inj₂ _ , _) _))
  rewrite vecZero≡inj {n} = ₂∼₂ _
reduceVector' xs ys (inj₁ pxs , pivXs) (inj₁ pys , pivYs) refl =
  ysn' , sameSpace , moreZeros≥Piv xs ysn' pivXs (findNonZero _ .proj₂) ysnXs<≡0 ysnXs≡0
  where
  open ReasonSetoid setoid

  vx = xs pxs
  vy = ys pxs
  xsn = vy *ₗ xs
  ysn = vx *ₗ ys
  ysn' = ysn -v xsn

  sameSpace : (span xs +ₛ span ys) ≅ (span xs +ₛ span ysn')
  sameSpace = sameMulitpliedBoth _ (pivXs .proj₁) _ _ _

  ysnXs<≡0 : ∀ i → i F.< pxs → ysn' i ≈ 0#
  ysnXs<≡0 i i<pxs = begin
    vx * ys i - vy * xs i ≈⟨ +-cong
      (*-congˡ (proj₂ pivYs i i<pxs))
      (-‿cong (*-congˡ (proj₂ pivXs i i<pxs))) ⟩
    vx * 0# - vy * 0# ≈⟨ +-cong (zeroʳ vx) (-‿cong (zeroʳ vy)) ⟩
    0# - 0# ≈⟨ -‿inverseʳ 0# ⟩
    0# ∎

  ysnXs≡0 : ysn' pxs ≈ 0#
  ysnXs≡0 = begin
    vx * vy - vy * vx ≈⟨ +-congˡ (-‿cong (*-comm vy _)) ⟩
    vx * vy - vx * vy ≈⟨ -‿inverseʳ (vx * vy) ⟩
    0# ∎

reduceVector : (xs ys : Vector F n)
  (let fxs = findNonZeroPos xs ; fys = findNonZeroPos ys)
  (xs≡ys : fxs ≡ fys)
  → Σ[ res ∈ Vector F n ] (((span xs +ₛ span ys) ≅ (span xs +ₛ span res)) × findNonZeroPos res ⊎> fys)
reduceVector xs ys xs≡ys = reduceVector' xs ys (findNonZero xs) (findNonZero ys) xs≡ys

V^n→Vec : Vector F m ^ n → Cᴹ {m} c
V^n→Vec {n = ℕ.zero} _ = 0ₛ
V^n→Vec {n = suc ℕ.zero} = span
V^n→Vec {n = suc (suc n)} (v , xs) = span v +ₛ V^n→Vec xs

_≐v_ : Rel (Vector F m ^ n) _
xs ≐v ys = V^n→Vec xs ≅ V^n→Vec ys

normalizeTwoLines' : (vecs : Vector F n ^ 2) →
  Σ[ res ∈ Vector F n ^ 2 ] (vecs ≐v res) ×
    normTwoVectors (vecs→zeroPos vecs) (vecs→zeroPos res)
normalizeTwoLines' tp@(xs , ys) with A.compare (findNonZeroPos xs) (findNonZeroPos ys)
... | tri< _ _ _ = tp , (id , id) , refl , refl
... | tri> _ _ _ = (ys , xs) , +ₛ-comm _ _ , refl , refl
... | tri≈ _ xs≡ys _ = let vred@(zs , same , prop) = reduceVector xs ys (Pointwise-≡⇒≡ xs≡ys) in
  (xs , zs) , same , refl , prop

Matrix : ℕ → ℕ → Set _
Matrix m n = Vec (Vector F m) n

MatrixData : ℕ → ℕ → Set _
MatrixData m n = Vec (Vec F m) n

matrix→matrixData : Matrix m n → MatrixData m n
matrix→matrixData = V.map toVec

matrixData→matrix : MatrixData m n → Matrix m n
matrixData→matrix = V.map fromVec

matrixZeros : Matrix m n → Vec (Fin⊤ m) n
matrixZeros = V.map findNonZeroPos

normMatrix : ∀ (xs : Matrix m n) i j i≢j →
  Σ[ ys ∈ Matrix m n ] (
    (vec→space xs ≅ vec→space ys) ×
    normalizeTwoLines i j i≢j (matrixZeros xs) (matrixZeros ys))
normMatrix {m} {n} xs i j i≢j = yss , swapSameVec {xs = xs} i≢j ysPropMod , lookupXs≢Ys , normVec
  where
  xsi = lookup xs i
  xsj = lookup xs j

  yst' = normalizeTwoLines' (xsi , xsj)
  ysPropMod = yst' .proj₂ .proj₁
  ysProp = yst' .proj₂ .proj₂
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
    open ≡-Reasoning

    helper = lookup yss k             ≡⟨ lookup∘update′ k≢j (xs [ i ]≔ ysi) _ ⟩
             lookup (xs [ i ]≔ ysi) k ≡⟨ lookup∘update′ k≢i xs _ ⟩
             lookup xs k              ∎

  sameNormTwoVectors : ∀ {p q r s} → p ≡ q → r ≡ s → normTwoVectors {m} p r → normTwoVectors q s
  sameNormTwoVectors refl refl ntv = ntv

  normVec : normTwoVectors _ _
  normVec = sameNormTwoVectors (×-≡,≡→≡ ((projSame _) , (projSame _))) (×-≡,≡→≡ (≡.sym α , ≡.sym β)) ysProp
    where
    open ≡-Reasoning

    projSame : ∀ i → findNonZeroPos (lookup xs i) ≡ lookup (V.map findNonZeroPos xs) i
    projSame i = ≡.sym (lookup-map i findNonZeroPos xs)

    lookupYssI≡ysi = lookup yss i             ≡⟨ lookup∘update′ i≢j (xs [ i ]≔ ysi) ysj ⟩
                     lookup (xs [ i ]≔ ysi) i ≡⟨ lookup∘update i xs _    ⟩
                     ysi ∎

    α = lookup (V.map findNonZeroPos yss) i ≡⟨ lookup-map i findNonZeroPos yss ⟩
        findNonZeroPos (lookup yss i)       ≡⟨ cong findNonZeroPos lookupYssI≡ysi ⟩
        findNonZeroPos ysi ∎

    β = lookup (matrixZeros yss) j    ≡⟨ lookup-map j findNonZeroPos yss ⟩
        findNonZeroPos (lookup yss j) ≡⟨ cong findNonZeroPos {y = ysj} (lookup∘update j (V.updateAt xs i (const ysi)) _) ⟩
        findNonZeroPos ysj            ∎

funcNorm : FuncNormAllLines m n (Matrix m (suc n))
numberZeros funcNorm = matrixZeros
normProps funcNorm = finProps
f (fNormLines funcNorm i j i≢j) xs = normMatrix xs i j i≢j .proj₁
nZerosProp (fNormLines funcNorm i j i≢j) xs = normMatrix xs i j i≢j .proj₂ .proj₂

MatrixS : (xs : Matrix m n) → Set _
MatrixS {m} {n} xs = Σ[ ys ∈ Matrix m n ] (vec→space xs ≅ vec→space ys)

normMatrixS : ∀ (xs : Matrix m n) (xs' : MatrixS xs) i j i≢j →
  Σ[ ys' ∈ MatrixS xs ]
    (normalizeTwoLines i j i≢j (matrixZeros (xs' .proj₁)) (matrixZeros (ys' .proj₁)))
normMatrixS xs (xss , vXs≃VXss) i j i≢j = let
  ys , vXss≅Vys , normed = normMatrix xss i j i≢j
  in (ys , ≐-trans vXs≃VXss vXss≅Vys) , normed

funcNormField : (xs : Matrix m (suc n)) → FuncNormAllLines m n (MatrixS xs)
numberZeros (funcNormField xs) (p , _) = matrixZeros p
normProps (funcNormField xs) = finProps
f (fNormLines (funcNormField xs) i j i≢j) zs@(ys , q) =
  normMatrixS xs zs i j i≢j .proj₁
nZerosProp (fNormLines (funcNormField xs) i j i≢j) zs =
 normMatrixS xs zs i j i≢j .proj₂

normalize : (xs : Matrix m n) → Σ[ ys ∈ Matrix m n ]
  (allLinesNormalized (matrixZeros ys) × (vec→space xs ≅ vec→space ys))
normalize {n = zero} V.[] = V.[] , (λ ()) , ≐-refl
normalize {n = suc n} xs =
  let (ys , normed) , sameVecSpace = normalizeA (funcNormField xs) (xs , ≐-refl)
  in ys , sameVecSpace , normed

normalizeD : MatrixData m n → MatrixData m n
normalizeD = matrix→matrixData ∘ proj₁ ∘ normalize ∘ matrixData→matrix
