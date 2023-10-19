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
open import Data.Nat.Properties as ℕ hiding (+-identityʳ; *-comm)
open import Data.Fin as F hiding (_-_)
open import Data.Fin.Properties as F
open import Data.Fin.Induction
open import Data.Vec.Functional as VF
open import Data.Vec.Functional.Properties as VF
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
open import MatrixNormalization.PropsAfter
import MatrixNormalization.FinInduction as FinInduction
open import MatrixNormalization.FinInductionAfter
import Algebra.Module.Instances.FunctionalVector as AMIF
import Algebra.SubModule as ASubMod
import Algebra.SubModule.Vec as ASubModVec
import Algebra.SubModule.Field as ASubModField
import Algebra.Apartness.Properties.HeytingCommutativeRing as HeytingProperties
import MatrixNormalization.normLinesField as NormField
open import MatrixNormalization.PropsAfterFin

open FuncNormAndZeros
open FuncNormAllLines
open module PNorm {n} = PropNorm (F.<-strictTotalOrder n) hiding (_≈_)
open PNormAfter

module MatrixNormalization.normLinesFieldAfter {c}
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
open NormField field' _≟_ ≈→∈
open import Algebra.HeytingField.Properties field'
open hFieldProps field'
open HeytingProperties heytingCommutativeRing

private variable
  m n : ℕ
  p px py : Fin⊤ n
  i j : Fin n
  xs ys : Vector F n

sameTwoValues : Rel (Fin⊤ n ^ 2) _
sameTwoValues (p , q) (r , s) = p ≡ r × q ≡ s

Lookup≢0Right : (xs : Vector F n) (p : Fin n) → Set _
Lookup≢0Right xs p = xs p # 0# × ∀ i → i F.> p → xs i ≈ 0#

VecPivotsRight' : (xs : Vector F n) → Set _
VecPivotsRight' {n} xs = (Σ[ p ∈ Fin n ] Lookup≢0Right xs p) ⊎ AllZeros xs

VecPivotPosRight : (xs : Vector F n) (p : Fin⊤ n) → Set c
VecPivotPosRight xs (inj₂ _) = AllZeros xs
VecPivotPosRight xs (inj₁ p) = Lookup≢0Right xs p

VecPivRight : Vector F n → Set _
VecPivRight xs = Σ[ p ∈ _ ] Lookup≢0Right xs p

VecPivotsRight : Vector F n → Set _
VecPivotsRight xs = Σ[ p ∈ _ ] VecPivotPosRight xs p

findNonZeroRight : (xs : Vector F n) → VecPivotsRight xs
findNonZeroRight {zero} xs = inj₂ _ , λ ()
findNonZeroRight {suc n} xs with xs (fromℕ _) ≟ 0# | findNonZeroRight (VF.removeAt xs (fromℕ _))
... | yes c#0 | _ = inj₁ (fromℕ _) , c#0 , (λ i i>n → ⊥-elim (≤⇒≯ (≤fromℕ _) i>n))
... | no  c≈0 | inj₂ _  , allZeros = inj₂ _ , all0Xs where
  all0Xs : AllZeros xs
  all0Xs p with p F.≟ fromℕ _
  ... | yes refl = tight _ _ .proj₁ c≈0
  ... | no   p≢n = begin
    xs p                     ≡˘⟨ VF.removeAt-punchOut xs (p≢n ∘ sym) ⟩
    VF.removeAt xs (fromℕ n) _ ≈⟨ allZeros _ ⟩
    0# ∎ where open ReasonSetoid setoid
... | no  c≈0 | inj₁ fn , xs#0 , xs≈0 = inj₁ pn , xs#0 , all0Xs where
  removeN = punchIn (fromℕ n)
  pn = removeN fn

  all0Xs : ∀ i → i F.> pn → xs i ≈ 0#
  all0Xs i i>fn with i F.≟ fromℕ _
  ... | yes refl = tight _ _ .proj₁ c≈0
  ... | no   i≢n = begin
    xs i ≡˘⟨ VF.removeAt-punchOut xs (i≢n ∘ sym) ⟩
    xs (removeN pI≢N) ≈⟨ xs≈0 pI≢N fn≤PIN ⟩
    0# ∎ where
      pI≢N = punchOut {i = fromℕ n} {i} (i≢n ∘ sym)

      fn≤PIN = begin
        suc (toℕ fn) ≡˘⟨ punchIn-fromℕ _ ⟩
        suc (toℕ (removeN fn)) ≤⟨ i>fn ⟩
        toℕ i ≡˘⟨ punchOut-fromℕ (i≢n ∘ sym) ⟩
        toℕ pI≢N ∎ where open ≤-Reasoning

      open ReasonSetoid setoid

findNonZeroPosRight : Vector F n → Fin⊤ _
findNonZeroPosRight = proj₁ ∘ findNonZeroRight

Lookup≢0→VecPivRight : (xs : Vector F n) (p : Fin n) → Lookup≢0 xs p → VecPivRight xs
Lookup≢0→VecPivRight xs p (left , _) with findNonZeroRight xs
... | inj₁ i , isPiv = i , isPiv
... | inj₂ y , allZ = ⊥-elim (tightʳ left (allZ p))

matrixZerosRight : Matrix n n → Vec (Fin⊤ n) n
matrixZerosRight = V.map findNonZeroPosRight

vecs→zeroPosRight : Vector F n ^ 2 → Fin⊤ _ ^ 2
vecs→zeroPosRight = VR.map findNonZeroPosRight _

alwaysSamePivotRight' : ∀ (xs : Vector F n) p₁ p₂ → Lookup≢0Right xs p₁ → Lookup≢0Right xs p₂ → p₁ ≡ p₂
alwaysSamePivotRight' xs p₁ p₂ (vpiv₁≢0 , vpiv₁≡0) (vpiv₂≢0 , vpiv₂≡0) with F.<-cmp p₁ p₂
... | tri< p₁<p₂ _ _ = ⊥-elim (tightʳ vpiv₂≢0 (vpiv₁≡0 p₂ p₁<p₂))
... | tri> _ _ p₁>p₂ = ⊥-elim (tightʳ vpiv₁≢0 (vpiv₂≡0 p₁ p₁>p₂))
... | tri≈ _ p₁≡p₂ _ = p₁≡p₂

alwaysSamePivotRight : ∀ (xs : Vector F n) p₁ p₂ → VecPivotPosRight xs p₁ → VecPivotPosRight xs p₂ → p₁ ≡ p₂
alwaysSamePivotRight xs (inj₁ x) (inj₂ y) (xsx≢0 , _) vpiv₂ = ⊥-elim (tightʳ xsx≢0 (vpiv₂ _))
alwaysSamePivotRight xs (inj₂ y) (inj₁ x) vpiv₁ (xsx≢0 , _) = ⊥-elim (tightʳ xsx≢0 (vpiv₁ _))
alwaysSamePivotRight xs (inj₂ y) (inj₂ y₁) vpiv₁ vpiv₂ = refl
alwaysSamePivotRight xs (inj₁ p₁) (inj₁ p₂) vpiv₁ vpiv₂ = cong inj₁ (alwaysSamePivotRight' xs _ _ vpiv₁ vpiv₂)

pivRight≥pivLeft : ∀ {xs : Vector F n} {p₁} {p₂} → Lookup≢0 xs p₁ → Lookup≢0Right xs p₂ → p₁ F.≤ p₂
pivRight≥pivLeft {xs = xs} {p₁} {p₂} (xp₁#0 , _) (_ , xp≈0) with F.<-cmp p₁ p₂
... | tri< p₁<p₂ _ _ = <⇒≤ p₁<p₂
... | tri≈ _ refl _ = F.≤-refl
... | tri> _ _ p₁>p₂ = ⊥-elim (tightʳ xp₁#0 (xp≈0 _ p₁>p₂))

findNonZeroRightEq : VecPivotPosRight xs p → findNonZeroPosRight xs ≡ p
findNonZeroRightEq {xs = xs} = alwaysSamePivotRight _ _ _ (findNonZeroRight xs .proj₂)

vecZeroRight≡inj : findNonZeroPosRight (vecZeros n) ≡ inj₂ _
vecZeroRight≡inj = findNonZeroRightEq {xs = vecZeros _} allZerosVecZero

moreZeros≤Piv : ∀ (xs ys : Vector F n)
  {px : Fin n} {py : Fin n} →
  Lookup≢0Right xs px → Lookup≢0Right ys py
  → (∀ i → i F.> px → ys i ≈ 0#)
  → ys px ≈ 0#
  → py F.< px
moreZeros≤Piv xs ys {px} {py} (ysX#0 , vPivX) (ysY#0 , vPivY) piv#0 piv≈0 with F.<-cmp px py
... | tri< px<py _ _ = ⊥-elim (tightʳ ysY#0 (piv#0 _ px<py))
... | tri≈ _ refl _  = ⊥-elim (tightʳ ysY#0 piv≈0)
... | tri> _ _ px>py = px>py

reduceVectorAfter' : ∀ (xs ys : Vector F n) {pxsR}
  (fxs : Lookup≢0Right xs pxsR) (fys : Lookup≢0Right ys pxsR)
  {pxs} (fxsL : Lookup≢0 xs pxs) {pys} (fysL : Lookup≢0 ys pys)
  (xsL>ysL : pxs F.> pys)
  → Σ[ res ∈ Vector F n ] Σ[ pivResRight ∈ Fin n ]
    ( Lookup≢0      res pys
    × Lookup≢0Right res pivResRight
    × pivResRight F.< pxsR
    × pys F.≤ pivResRight)
reduceVectorAfter' xs ys {pxs} pivX@(vx#0 , pxs<≈0) (pivR#0 , pivR≈0)
  (pxsL#0 , i<pxs≈0) {pysL} (pysL#0 , i<pys≈0) xsL>ysL =
  ysn' , _ , pivYsnL , pivRightProve , moreZeros≤Piv xs ysn' pivX pivRightProve ysnXs>≡0 ysnXs≡0 ,
  pivRight≥pivLeft pivYsnL pivRightProve
  where
  open ReasonSetoid setoid

  vx = xs pxs
  vy = ys pxs
  xsn = vy *ₗ xs
  ysn = vx *ₗ ys
  ysn' = ysn -v xsn

  ysnL' : ysn' pysL ≈ vx * ys pysL
  ysnL' = begin
    vx * ys pysL - vy * xs pysL ≈⟨ +-congˡ (-‿cong (*-congˡ (i<pxs≈0 _ xsL>ysL))) ⟩
    vx * ys pysL - vy * 0#      ≈⟨ +-congˡ (-‿cong (zeroʳ _)) ⟩
    vx * ys pysL - 0#           ≈⟨ +-congˡ -0#≈0# ⟩
    _                           ≈⟨ +-identityʳ (vx * ys pysL) ⟩
    vx * ys pysL ∎

  ysnL'' : vx * ys pysL ≈ ysn' pysL
  ysnL'' = begin _ ≈˘⟨ ysnL' ⟩ _ ∎

  ysnL#0 : ysn' pysL # 0#
  ysnL#0 = cong-# ysnL'' (x#0y#0→xy#0 vx#0 pysL#0)

  ysnL<≈0 : ∀ i → i F.< pysL → ysn' i ≈ 0#
  ysnL<≈0 i i<pysL = begin
    vx * ys i - vy * xs i ≈⟨ +-cong
      (*-congˡ (i<pys≈0 _ i<pysL))
      (-‿cong (*-congˡ (i<pxs≈0 _ (F.<-trans i<pysL xsL>ysL)))) ⟩
    vx * 0# - vy * 0# ≈⟨ +-cong (zeroʳ vx) (-‿cong (zeroʳ vy)) ⟩
    0# - 0# ≈⟨ -‿inverseʳ 0# ⟩
    0# ∎

  pivYsnL : Lookup≢0 ysn' pysL
  pivYsnL = ysnL#0 , ysnL<≈0

  ysnXs>≡0 : ∀ i → i F.> pxs → ysn' i ≈ 0#
  ysnXs>≡0 i i>pxs = begin
    vx * ys i - vy * xs i ≈⟨ +-cong (*-congˡ (pivR≈0 _ i>pxs)) (-‿cong (*-congˡ (pxs<≈0 _ i>pxs))) ⟩
    vx * 0# - vy * 0#     ≈⟨ +-cong (zeroʳ _) (-‿cong (zeroʳ _)) ⟩
    0# - 0#               ≈⟨ -‿inverseʳ _ ⟩
    0# ∎

  ysnXs≡0 : ysn' pxs ≈ 0#
  ysnXs≡0 = begin
    vx * vy - vy * vx ≈⟨ +-congˡ (-‿cong (*-comm _ _)) ⟩
    vx * vy - vx * vy ≈⟨ -‿inverseʳ (vx * vy) ⟩
    0# ∎

  ΣpivRight : Σ[ pivResRight ∈ Fin _ ] Lookup≢0Right ysn' pivResRight
  ΣpivRight with findNonZeroRight ysn'
  ... | inj₁ pivResRight , prove = pivResRight , prove
  ... | inj₂ _ , allZ = ⊥-elim (tightʳ ysnL#0 (allZ _))

  pivResRight = ΣpivRight .proj₁

  pivRightProve : Lookup≢0Right ysn' pivResRight
  pivRightProve = ΣpivRight .proj₂

reduceVectorAfter : ∀ (xs ys : Vector F n) {pxsR}
  (fxs : Lookup≢0Right xs pxsR) {pysR} (fys : Lookup≢0Right ys pysR)
  (xs≥ys : pxsR F.≥ pysR) {pxs} (fxsL : Lookup≢0 xs pxs) {pys} (fysL : Lookup≢0 ys pys)
  (xsL>ysL : pxs F.> pys)
  → Σ[ res ∈ Vector F n ] Σ[ pivResRight ∈ Fin n ]
    ( Lookup≢0      res pys
    × Lookup≢0Right res pivResRight
    × pivResRight F.< pxsR
    × pys F.≤ pivResRight)
reduceVectorAfter xs ys {pxR} fxs {pyR} fys xs≥ys fxsL {pys} fysL xsL>ysL with F.<-cmp pxR pyR
... | tri< pxR<pyR _ _ = ⊥-elim (≤⇒≯ xs≥ys pxR<pyR)
... | tri≈ _ refl _ = reduceVectorAfter' xs ys fxs fys fxsL fysL xsL>ysL
... | tri> _ _ pxR>pyR = ys , pyR , fysL , fys , pxR>pyR , pivRight≥pivLeft fysL fys


record VecNorm (n : ℕ) : Set c where
  field
    vec : Vector F n
    pivL : Fin n
    pivR : Fin n
    isPivL : Lookup≢0 vec pivL
    isPivR : Lookup≢0Right vec pivR

  pivL≤pivR : pivL F.≤ pivR
  pivL≤pivR = pivRight≥pivLeft isPivL isPivR

open VecNorm

pivL≡i : (xs : VecNorm n) (i : Fin n) → Set _
pivL≡i xs i = Lookup≢0 (vec xs) i

MatrixNorm : ℕ → Set _
MatrixNorm n = Σ[ xs ∈ Vec (VecNorm n) n ] (∀ i → pivL≡i (lookup xs i) i)

pivRightsVec : Vec (VecNorm n) n → Vec (Fin n) n
pivRightsVec = V.map pivR

pivRights : MatrixNorm n → Vec (Fin n) n
pivRights = pivRightsVec ∘ proj₁

vec→VecNormBoth : (xs : Vector F n) → Lookup≢0 xs i → Lookup≢0Right xs j → VecNorm n
vec (vec→VecNormBoth xs pleft pright) = xs
pivL (vec→VecNormBoth xs pleft pright) = _
pivR (vec→VecNormBoth xs pleft pright) = _
isPivL (vec→VecNormBoth xs pleft pright) = pleft
isPivR (vec→VecNormBoth xs pleft pright) = pright

vec→VecNorm : (xs : Vector F n) → Lookup≢0 xs i → VecNorm n
vec→VecNorm xs pleft = vec→VecNormBoth xs pleft (Lookup≢0→VecPivRight xs _ pleft .proj₂)

normMatrixRight : ∀ (xss : MatrixNorm (ℕ.suc n)) i j i>j →
  LinesNormalizedAfterIJ i (suc j) i>j (pivRights xss) →
  Σ[ ys ∈ MatrixNorm (ℕ.suc n) ] NormalizeTwoLines i (inject₁ j) (i>j→i>injJ i>j)
    (pivRights xss) (pivRights ys)
normMatrixRight xss@(xs , xsIL≡i) i j i>j norm@(normBef , _) =
  (ysn , pivLYs≡i) , normFirst , normSecond
  where

  xsi = lookup xs i
  xsj = lookup xs (inject₁ j)

  mxs = pivRights xss

  mxs≥i : GreaterThanI mxs
  mxs≥i i = begin
    toℕ i ≡⟨ cong toℕ (alwaysSamePivot' _ _ _ (xsIL≡i i) (isPivL (lookup xs i))) ⟩
    toℕ (pivL (lookup xs i)) ≤⟨ pivL≤pivR ((lookup xs i)) ⟩
    toℕ (pivR (lookup xs i)) ≡˘⟨ cong toℕ (V.lookup-map i pivR xs) ⟩
    toℕ (lookup mxs i) ∎
    where open ≤-Reasoning

  pxsI≥pxsJ' : lookup mxs (inject₁ j) F.≤ lookup mxs i
  pxsI≥pxsJ' = xsJ≤xsI {xs = mxs} (i>j→i>injJ i>j) mxs≥i normBef

  pxsI≥pxsJ : pivR xsi F.≥ pivR xsj
  pxsI≥pxsJ rewrite sym (V.lookup-map i pivR xs) | sym (V.lookup-map (inject₁ j) pivR xs) = pxsI≥pxsJ'

  ysjProps = reduceVectorAfter (xsi .vec) (xsj .vec) (xsi .isPivR) (xsj .isPivR)
    pxsI≥pxsJ (xsIL≡i i) (xsIL≡i _) (i>j→i>injJ i>j)

  yp = ysjProps .proj₁
  ypNorm = vec→VecNormBoth yp (ysjProps .proj₂ .proj₂ .proj₁) (ysjProps .proj₂ .proj₂ .proj₂ .proj₁)
  ysn = xs [ inject₁ j ]≔ ypNorm

  pivLYs≡i : ∀ i → pivL≡i (lookup ysn i) i
  pivLYs≡i i with i F.≟ inject₁ j
  ... | yes refl rewrite lookup∘update i xs ypNorm = ysjProps .proj₂ .proj₂ .proj₁
  ... | no i≢j rewrite lookup∘update′ i≢j xs ypNorm = xsIL≡i _

  normFirst : ∀ k → k ≢ inject₁ j → lookup (pivRightsVec ysn) k ≡ lookup (pivRightsVec xs) k
  normFirst k k≢j = begin
    lookup (pivRightsVec ysn) k ≡⟨ V.lookup-map k pivR ysn ⟩
    pivR (lookup ysn k)         ≡⟨ cong pivR (lookup∘update′ k≢j xs _) ⟩
    pivR (lookup xs k)         ≡˘⟨ V.lookup-map k pivR xs ⟩
    lookup (pivRightsVec xs) k ∎
    where open ≡-Reasoning

  normSecond : lookup (pivRightsVec xs) i F.> lookup (pivRightsVec ysn) (inject₁ j)
  normSecond = begin-strict
    toℕ (lookup (pivRightsVec ysn) (inject₁ j)) ≡⟨ cong toℕ (V.lookup-map (inject₁ j) pivR ysn) ⟩
    toℕ (pivR (lookup ysn (inject₁ j))) ≡⟨ cong (toℕ ∘ pivR) (lookup∘update (inject₁ j) xs _) ⟩
    toℕ (pivR ypNorm) ≡⟨⟩
    toℕ (ysjProps .proj₂ .proj₁) <⟨ ysjProps .proj₂ .proj₂ .proj₂ .proj₂ .proj₁ ⟩
    toℕ (pivR (lookup xs i)) ≡˘⟨ cong toℕ (V.lookup-map i pivR xs) ⟩
    toℕ (lookup (pivRightsVec xs) i) ∎
    where open ≤-Reasoning

funcNormAfter : FuncNormAllLines n (MatrixNorm (suc n))
numberZeros funcNormAfter = pivRights
normProps funcNormAfter = finPropsInvNewRight
f (fNormLines funcNormAfter i j i>j) xs ha = normMatrixRight xs i j i>j ha .proj₁
nZerosProp (fNormLines funcNormAfter i j i>j) xs ha = normMatrixRight xs i j i>j ha .proj₂

normAllRight : MatrixNorm (suc n) → Σ[ ys ∈ MatrixNorm (suc n) ] AllLinesNormalizedRight (pivRights ys)
normAllRight {n} xs = normalizeA {m = n} funcNormAfter xs
