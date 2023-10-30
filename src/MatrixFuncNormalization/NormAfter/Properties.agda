{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.NormAfter.Properties {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Level using (Level; Lift; lift; _⊔_; 0ℓ)
open import Function hiding (flip)
open import Data.Bool using (Bool; false; true; T)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; maybe′; just)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (≰⇒>)
open import Data.Fin.Base as F hiding (_+_; _-_; lift; zero; suc)
open import Data.Fin.Patterns
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Sum
open import Data.Vec.Functional as V
open import Data.Vec.Functional.Properties
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as EqSetoids
open import Algebra
import Algebra.Properties.Ring as RingProps
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; refl; subst)
open import Relation.Binary.Construct.Add.Infimum.Strict hiding (_<₋_)
import Relation.Binary.Construct.Add.Point.Equality as Equality
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Construct.Add.Infimum as ₋
open import Relation.Nullary.Construct.Add.Supremum
import Relation.Binary.Construct.Add.Supremum.Strict as <⁺′
import Relation.Binary.Construct.Add.Supremum.NonStrict as ≤⁺′
import Relation.Binary.Construct.Add.Infimum.Strict as <₋′
import Algebra.Module.Instances.FunctionalVector as AMIF
import Algebra.Apartness.Properties.HeytingCommutativeRing as HCRProps

open import Vector.Base as V
open import Algebra.Matrix
open import Algebra.MatrixData renaming (Matrix to MatrixData)
import Algebra.HeytingField.Properties as HFProps
import MatrixFuncNormalization.MatrixProps as MatrixPropsBefore
import MatrixFuncNormalization.MatrixPropsAfter as MatrixPropsAfter
import MatrixFuncNormalization.normBef as NormBef
import MatrixFuncNormalization.NormAfter.Base as NormAfterBase
open import MatrixFuncNormalization.FinInduction
import Algebra.Module.VecSpace as VecSpace
open import lbry

open NormAfterBase hField _≟_
open hFieldProps hField
open HFProps hField
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open NormBef hField _≟_ using (normalizeMatrix; AllZeros; _-v_; sameVecPiv; alwaysSamePivot)
  renaming ( VecPivotPos to VecPivotPosLeft
           ; Lookup≢0 to Lookup≢0Left
           ; normTwoRows to normTwoRowsLeft
           ; MatrixPivots to MatrixPivotsLeft
           ; findNonZero to findNonZeroLeft
           )
open M hiding (_+ᴹ_)
open PVec
open PNormBef using (NormedTwoBeforeAfter; NormedTwoBeforeAfter′; compare⊤⁺; _>′_)
open PNormAfter using (_<′_; AllRowsNormalizedRight; simpleFinProps)
open HCRProps heytingCommutativeRing
open RingProps ring
open ≋‵ using (≋-setoid)
open ≋
open FuncNormAllLines
open FuncNormAndZeros
open module PNorm {n} = MatrixPropsBefore (<-strictTotalOrder n)
  using (BothRowsAreNormalize; DifferentIndicesAreEqual; NormedTwoBeforeAfter‵)
open module ≈∙ {a} {A} = Equality {a} {A = A} _≡_ using (_≈∙_; ∙≈∙; [≈]-injective)
  renaming (≈∙-isEquivalence to ≈∙-isEquivalence′)
open module ≤⁺ {n} = ≤⁺′ (F._≤_ {n}) using (_≤⁺_)
open module <⁺ {n} = <⁺′ (F._<_ {n}) using (_<⁺_)
open module <₋ {n} = <₋′ (F._<_ {n}) using (_<₋_)

private variable
  ℓ ℓ′ : Level
  A : Set ℓ
  m m′ n n′ : ℕ

private
  VerifiyIfTrue : Bool → Set ℓ → Set ℓ
  VerifiyIfTrue false _ = ⊤
  VerifiyIfTrue true = id

  ≈∙-isEquivalence : IsEquivalence (_≈∙_ {A = A})
  ≈∙-isEquivalence = ≈∙-isEquivalence′ ≡.isEquivalence

open module ≈∙-equiv {ℓ} {A} = IsEquivalence (≈∙-isEquivalence {ℓ} {A = A})
  renaming
  ( refl  to ≈∙-refl
  ; sym   to ≈∙-sym
  ; trans to ≈∙-trans
  ; reflexive to ≈∙-reflexive
  )

Maybe≈0 : Vector F n → Fin n ₋ → Set _
Maybe≈0 xs ⊥₋ = ⊤
Maybe≈0 xs [ i ] = xs i ≈ 0#

Lookup≢0 : (xs : Vector F n) (p : Fin n) (x : F) (x#0 : x # 0#)  → Set _
Lookup≢0 xs p x x#0 = x ≈ xs p × ∀ i → i > p → xs i ≈ 0#

VecPivots' : (xs : Vector F n) → Set _
VecPivots' xs = (Σ[ p ∈ Fin _ ] Σ[ x ∈ F ] Σ[ x#0 ∈ x # 0# ] Lookup≢0 xs p _ x#0) ⊎ AllZeros xs

VecPivotPos : (xs : Vector F n) (p : Fin n ₋) (pivValue : PivValue p) → Set ℓ₁
VecPivotPos xs    ⊥₋ _ = AllZeros xs
VecPivotPos xs [ p ] (_ , piv#0) = Lookup≢0 xs p _ piv#0

VecPivotPosΣ : ∀ n → Set _
VecPivotPosΣ n = Σ[ xs ∈ Vector F n ] Σ[ p ∈ Fin n ₋ ] Σ[ pivValue ∈ PivValue p ] VecPivotPos xs p pivValue

PivLeft≤PivRight : ∀ {xs : Vector F n} {pₗ pᵣ : Fin n} {x} {x#0} → Lookup≢0Left xs pₗ → Lookup≢0 xs pᵣ x x#0 → pₗ ≤ pᵣ
PivLeft≤PivRight {xs = xs} {pₗ} {pᵣ} {x} {x#0} (pₗ#0 , pₗ≈0) (x≈pr , pᵣ≈0) with pₗ ≤? pᵣ
... | yes pₗ≤pᵣ = pₗ≤pᵣ
... | no ¬pₗ≤pᵣ = tightBoth (cong-# x≈pr x#0) (pₗ≈0 pᵣ pₗ>pᵣ)
  where pₗ>pᵣ = ≰⇒> ¬pₗ≤pᵣ

normTwoRowsPropsVecPiv : ∀ {xs ys : Vector F n} {px py : Fin n ₋} {vx} {vy}
  (fxs : VecPivotPos xs px vx) (fys : VecPivotPos ys py vy)
  → px <′ py
  → let ys′ = normTwoRows xs ys px py vx in
    VecPivotPos ys′ py vy
normTwoRowsPropsVecPiv {ys = ys} {⊥₋} _ fys _ = fys
normTwoRowsPropsVecPiv {xs = xs} {ys} px′@{[ px ]} py′@{[ py ]} vx′@{vx , vx#0} {_ , vy#0}
  (vx≈xsPx , fxs) (vy≈ysPy , fys) (inj₂ [ px<py ]) =

  ≈.trans vy≈ysPy (≈.sym ysnPy≈ysPy) , ysnXs>≈0
  where
  open ≈-Reasoning

  vx⁻¹ = #⇒invertible vx#0 .proj₁
  vy = ys px

  -vx⁻¹vy = - (vy * vx⁻¹)
  xsn = -vx⁻¹vy *ₗ xs
  ysn = normTwoRows xs ys px′ py′ vx′
  xvx = xs px

  ysnPy≈ysPy : ysn py ≈ ys py
  ysnPy≈ysPy = begin
    ys py + _ * xs py ≈⟨ +-congˡ  (*-congˡ (fxs _ px<py)) ⟩
    ys py + _ * 0# ≈⟨ +-congˡ (zeroʳ _) ⟩
    ys py + 0# ≈⟨ +-identityʳ _ ⟩
    ys py ∎

  ysnXs>≈0 : ∀ i → i > py → ysn i ≈ 0#
  ysnXs>≈0 i i>pxs = begin
    ys i + -vx⁻¹vy * xs i ≈⟨ +-cong (fys i i>pxs) (*-congˡ (fxs _ (<-trans px<py i>pxs))) ⟩
      0# + -vx⁻¹vy *   0# ≈⟨ +-congˡ (zeroʳ _) ⟩
      0# +             0# ≈⟨ +-identityʳ 0# ⟩
      0# ∎

normTwoRowsPropsMaybe : ∀ {xs ys : Vector F n} {px py : Fin n ₋} {vx} {vy}
  (fxs : VecPivotPos xs px vx) (fys : VecPivotPos ys py vy)
  → px <′ py
  → let ys′ = normTwoRows xs ys px py vx in
    Maybe≈0 ys′ px
normTwoRowsPropsMaybe {ys = ys} {⊥₋} _ fys _ = _
normTwoRowsPropsMaybe {xs = xs} {ys} px′@{[ px ]} py′@{[ py ]} vx′@{vx , vx#0} {_ , vy#0}
  (vx≈xsPx , fxs) (vy≈ysPy , fys) (inj₂ _) =

  ysnXs≈0
  where
  open ≈-Reasoning

  vx⁻¹ = #⇒invertible vx#0 .proj₁
  vy = ys px

  ysn = normTwoRows xs ys px′ py′ vx′
  xvx = xs px

  α = begin
    vy * vx⁻¹ * xvx    ≈⟨ *-assoc _ _ _ ⟩
    vy * (vx⁻¹ * xvx) ≈˘⟨ *-congˡ (*-congˡ vx≈xsPx) ⟩
    vy * (vx⁻¹ * vx)   ≈⟨ *-congˡ (x#0→x⁻¹*x≈1 vx#0) ⟩
    vy * 1#            ≈⟨ *-identityʳ _ ⟩
    vy ∎

  vyvx⁻¹vx≈vy = begin
    - (vy * vx⁻¹) * xvx ≈˘⟨ -‿distribˡ-* _ _ ⟩
    - (vy * vx⁻¹ * xvx)  ≈⟨ -‿cong α ⟩
    - vy ∎

  ysnXs≈0 : ysn px ≈ 0#
  ysnXs≈0 = begin
    vy + - (vy * vx⁻¹) * xvx ≈⟨ +-congˡ vyvx⁻¹vx≈vy  ⟩
    vy + - vy                ≈⟨ -‿inverseʳ _ ⟩
    0# ∎

MatrixPivots : Matrix F n m → Vector (PivWithValue m) n → Set _
MatrixPivots xs pivsXs = ∀ i → VecPivotPos (xs i) (pivsXs i .proj₁) (pivsXs i .proj₂)

MatrixWithPivots : (n m : ℕ) → Set _
MatrixWithPivots n m = Σ[ xs ∈ Matrix F n m ] Σ[ pivs ∈ Vector (PivWithValue m) n ] MatrixPivots xs pivs

matrixPivs : MatrixWithPivots n m → Vector (Fin m ₋) n
matrixPivs (_ , pivs , _) i = pivs i .proj₁

pivsWV→pivs : Vector (PivWithValue m) n → Vector (Fin m ₋) n
pivsWV→pivs xs i = proj₁ (xs i)

normMatrixTwoRowsPropsVecPos : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs) (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (i j : Fin n) (i<j : i < j) (k : Fin n) (k≟j : Bool) (ref : Reflects (k ≡ j) k≟j) →
    let ys = normMatrixTwoRowsF′ xs pivsXs i j k k≟j in
    VecPivotPos ys (pivs k) (pivsXs k .proj₂)
normMatrixTwoRowsPropsVecPos xs pivsXs mXsPivs allRowsNormedRight i j i<j .j true (ofʸ ≡.refl) =
 normTwoRowsPropsVecPiv (mXsPivs _) (mXsPivs _) (allRowsNormedRight _ _ i<j)
normMatrixTwoRowsPropsVecPos xs pivsXs mXsPivs allRowsNormedRight i j i<j k false (ofⁿ _) = mXsPivs k

normMatrixTwoRowsPropsMaybe : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs) (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (i j : Fin n) (i<j : i < j) (k : Fin n) (ref : Reflects (k ≡ j) true) →
    let ys = normMatrixTwoRowsF′ xs pivsXs i j k true in
      Maybe≈0 ys (pivs i)
normMatrixTwoRowsPropsMaybe xs pivsXs mXsPivs allRowsNormedRight i j i<j _ (ofʸ ≡.refl) =
  normTwoRowsPropsMaybe (mXsPivs _) (mXsPivs _) (allRowsNormedRight _ _ i<j)

ListFin : ℕ → Set _
ListFin m = ListVec (Fin m)

filterPivsWithValues : Vector (PivWithValue m) n → ListFin m
filterPivsWithValues {n = zero} xs = -, []
filterPivsWithValues {n = suc n} xs with xs 0F .proj₁
... | [ x ] = -, x ∷ filterPivsWithValues (tail xs) .proj₂
... | ⊥₋    = -, []

filterPivs : Vector (Fin m ₋) n → ListFin m
filterPivs {n = zero} xs = -, []
filterPivs {n = suc n} xs with xs 0F
... | [ x ] = -, x ∷ filterPivs (tail xs) .proj₂
... | ⊥₋    = -, []

ColumnsOfMatrix : (xs : Matrix F n m) (cols : Vector (Fin m) n′) (ys : Matrix F n n′) → Set _
ColumnsOfMatrix xs cols ys = ∀ i j → ys i j ≡ xs i (cols j)

ColumnsFinOfMatrix : (xs : Matrix F n m) {m′ : ℕ} (fm′m : Fin m′ → Fin m) (ys : Matrix F n m′) → Set _
ColumnsFinOfMatrix xs fm′m ys = ∀ i j → ys i j ≡ xs i (fm′m j)

normMatrixTwoRowsPivots : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs) (mXsPivs : MatrixPivots xs pivsXs)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (i j : Fin n) (i<j : i < j) → let ys = normMatrixTwoRowsF xs pivsXs i j in
    MatrixPivots ys pivsXs
normMatrixTwoRowsPivots xs pivsXs mXsPivs allRowsNormedRight i j i<j k =
  normMatrixTwoRowsPropsVecPos xs pivsXs mXsPivs allRowsNormedRight i j i<j k _ (proof $ k F.≟ j)

normMatrixTwoRowsMaybe : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs) (mXsPivs : MatrixPivots xs pivsXs)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (i j : Fin n) (i<j : i < j) → let ys = normMatrixTwoRowsF xs pivsXs i j in
    Maybe≈0 (ys j) (pivs i)
normMatrixTwoRowsMaybe xs pivsXs mXsPivs allRowsNormedRight i j i<j
  rewrite dec-true (j F.≟ j) ≡.refl
  = normMatrixTwoRowsPropsMaybe xs pivsXs mXsPivs allRowsNormedRight i j i<j j (ofʸ ≡.refl)

normMatrixTwoRows≈ⱽ : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (i j : Fin n) (i<j : i < j) → let ys = normMatrixTwoRowsF xs pivsXs i j in
    xs ≈ⱽ ys
normMatrixTwoRows≈ⱽ xs pivsXs i j i<j with pivsXs i in pivEq
... | ⊥₋ , _ = idR helper
  where
  helper : xs ≋ λ k → normMatrixTwoRowsF′ xs pivsXs i j k (does (k F.≟ j))
  helper k p with k F.≟ j
  ... | yes ≡.refl rewrite pivEq = ≈.refl
  ... | no  k≢j = ≈.refl
... | [ pivI ] , vi , vi#0 = rec mOps (idR ≋-refl) xsOp≈zs
  where

  vj = xs j pivI

  vi⁻¹ = #⇒invertible vi#0 .proj₁
  -vi⁻¹vj = - (vj * vi⁻¹)

  mOps = addCons i j (<⇒≢ i<j) _

  zs = normMatrixTwoRowsF xs pivsXs i j

  xsOp≈zs : xs [ j ]← -vi⁻¹vj *[ i ] ≋ zs
  xsOp≈zs k p with k F.≟ j
  ... | yes ≡.refl rewrite dec-true (k F.≟ k) ≡.refl | pivEq = ≈.refl
  ... | no k≢j rewrite dec-false (j F.≟ k) (k≢j ∘ ≡.sym) = ≈.refl

findSubMatrix : (pivsXs : Vector (PivWithValue m) n) → Σ[ m′ ∈ ℕ ] Vector (Fin m) m′
findSubMatrix {n = zero} pivsXs = ℕ.zero , []
findSubMatrix {n = ℕ.suc n} pivsXs with pivsXs 0F .proj₁
... | ⊥₋ = findSubMatrix $ tail pivsXs
... | just p = let n , xs = findSubMatrix $ tail pivsXs in suc n , p ∷ xs


private
  <⁺→≤⁺ : {i j : Fin n ⁺} → i <⁺ j → i ≤⁺ j
  <⁺→≤⁺ <⁺′.[ i<j ] = ≤⁺′.[ ℕ.<⇒≤ i<j ]
  <⁺→≤⁺ <⁺′.[ k ]<⊤⁺ = just k ≤⁺′.≤⊤⁺

  <⁺→¬≥⁺ : {i j : Fin n ⁺} → i <⁺ j → ¬ (j ≤⁺ i)
  <⁺→¬≥⁺ <⁺′.[ i<j ] ≤⁺′.[ i≥j ] = ℕ.<⇒≱ i<j i≥j

subMatrix : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (fm′m : Fin m′ → Fin m) (i j : Fin n) → Matrix F n m′
subMatrix xs pivsXs fm′m i j k p = normMatrixTwoRowsF xs pivsXs i j k (fm′m p)

pivsSubMatrix : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (pivsOfPivMatrix : Vector (Fin m′ ⁺) n)
  (fm′m : Fin m′ → Fin m) (i j : Fin n) → Vector (Fin m′ ⁺) n
pivsSubMatrix xs pivsXs pivsOfPivMatrix fm′m i j k with does $ k F.≟ j
... | false = pivsOfPivMatrix k
... | true  = proj₁ $ findNonZeroLeft $ subMatrix xs pivsXs fm′m i j j

normMatrixTwoRowsMPivots : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (fm′m : Fin m′ → Fin m)
  (pivsMatrix : Matrix F n m′) (isColMatrix : ColumnsFinOfMatrix xs fm′m pivsMatrix)
  (pivsOfPivMatrix : Vector (Fin m′ ⁺) n)
  (mPivsOfPivMatrix : MatrixPivotsLeft pivsMatrix pivsOfPivMatrix) (i j : Fin n)
  (let ysPM = subMatrix xs pivsXs fm′m i j; ysPMpivs = pivsSubMatrix xs pivsXs pivsOfPivMatrix fm′m i j)
  → MatrixPivotsLeft ysPM ysPMpivs
normMatrixTwoRowsMPivots xs pivsXs fm′m _ isColMatrix _ mPivsOfPivMatrix i j k
  with k F.≟ j
... | no  _ = sameVecPiv (isColMatrix k) (mPivsOfPivMatrix k)
... | yes refl = sameVecPiv sameEq $ proj₂ $ findNonZeroLeft $ zs j
  where
  zs    = subMatrix xs pivsXs fm′m i j
  sameEq : ∀ p → zs j p ≡
      normTwoRows (xs i) (xs j) (pivsXs i .proj₁) (pivsXs j .proj₁)
      (pivsXs i .proj₂) (fm′m p)
  sameEq p  = ≡.cong (λ x → normMatrixTwoRowsF′ xs pivsXs i j j x (fm′m p)) (dec-true (j F.≟ j) ≡.refl)


subMatrixDiffIndices : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (fm′m : Fin m′ → Fin m) (pivsOfPivMatrix : Vector (Fin m′ ⁺) n) (i j : Fin n)
  (let ysPMpivs = pivsSubMatrix xs pivsXs pivsOfPivMatrix fm′m i j)
  → DifferentIndicesAreEqual i j pivsOfPivMatrix ysPMpivs
subMatrixDiffIndices xs pivsXs fm′m pivsOfPivMatrix i j k _ k≢j
  rewrite dec-false (k F.≟ j) k≢j = ≈∙-refl

subMatrixNormedBeforeAfter : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (fm′m : Fin m′ → Fin m)
  (ys : Matrix F n m′) (isColXsYs : ColumnsFinOfMatrix xs fm′m ys)
  (pivsYs : Vector (Fin m′ ⁺) n)
  (mPivsYs : MatrixPivotsLeft ys pivsYs)
  (i j : Fin n) (i<j : i < j) (pivs≤ : pivsYs i ≤⁺ pivsYs j)
  (let pivsZs = pivsSubMatrix xs pivsXs pivsYs fm′m i j)
  → NormedTwoBeforeAfter‵ i j (<⇒≢ i<j) pivsYs pivsZs
subMatrixNormedBeforeAfter xs pivsXs mXsPivs allRowsNormedRight fm′m ys isColXsYs pivsYs mPivsYs i j i<j pivs≤ = helper
  where
  zs = subMatrix xs pivsXs fm′m i j
  pivZs = pivsSubMatrix xs pivsXs pivsYs fm′m i j
  i≢j = <⇒≢ i<j

  pivZsI≈pivMi : pivZs i ≈∙ pivsYs i
  pivZsI≈pivMi rewrite dec-false (i F.≟ j) i≢j = ≈∙-refl

  helper : _
  helper with pivsXs i in pivIEq | pivsXs j in pivJEq | compare⊤⁺ (pivsYs i) (pivsYs j) in compareEq
  ... | _ | _ | tri< pI<⁺pJ ¬b ¬c = subst (NormedTwoBeforeAfter′ (pivZs i) (pivZs j)) (≡.sym compareEq) $ lift $ pivZsI≈pivMi , {!!}
  -- lift (pivZsI≈pivMi , pivZsJ≈pivMj)
    where

    open ≈-Reasoning

    normTwoRows≡ : ∀ p → normTwoRows (xs i) (xs j) (pivsXs i .proj₁) (pivsXs j .proj₁)
           (pivsXs i .proj₂) (fm′m p) ≈ xs j (fm′m p)
    normTwoRows≡ p with pivsXs i in pivIEq
    ... | ⊥₋ , _ rewrite pivIEq = ≈.refl
    ... | just pivI , p₁ , p₂ rewrite pivIEq = begin
      xs j (fm′m p) + - (xs j pivI * _) * _
        ≈⟨ +-congˡ (begin
                      _      ≈⟨ *-congʳ (≈.trans (-‿cong $ ≈.trans (*-congʳ xsJPivI≈0#) $ zeroˡ _) -0#≈0#) ⟩
                      0# * _ ≈⟨ zeroˡ _ ⟩
                      _ ∎ ) ⟩
      xs j (fm′m p) + 0# ≈⟨ +-identityʳ _ ⟩
      xs j (fm′m p) ∎

      where

      pivXsI<pivXsJ : just pivI <′ pivsXs j .proj₁
      pivXsI<pivXsJ = helper3 (allRowsNormedRight _ _ i<j)
        where
        helper3 : pivsXs i .proj₁ <′ pivsXs j .proj₁ → just pivI <′ pivsXs j .proj₁
        helper3 rewrite pivIEq = id

      pivXsI<₋pivXsJ : just pivI <₋ pivsXs j .proj₁
      pivXsI<₋pivXsJ with pivXsI<pivXsJ
      ... | inj₁ (xsI≈⊥ , _) = contradiction xsI≈⊥ λ ()
      ... | inj₂ pivI<pivJ = pivI<pivJ

      help3 : VecPivotPos (xs j) (pivsXs j .proj₁) (pivsXs j .proj₂) → xs j pivI ≈ 0#
      help3 vecPiv = {!!}

      -- help5 : VecPivotPosLeft (xs j) {!!}  → xs j pivI ≈ 0#
      -- help5 = {!!}

      xsJPivI≈0# : xs j pivI ≈ 0#
      xsJPivI≈0# = help3 $ mXsPivs j

    normTwoRowsJ≡0 : normTwoRows (xs i) (xs j) (pivsXs i .proj₁) (pivsXs j .proj₁)
           (pivsXs i .proj₂) {!!} ≈ 0#
    normTwoRowsJ≡0 = {!!}

    vecPivXsZs : VecPivotPosLeft (xs j ∘ fm′m) (pivZs j)
    vecPivXsZs rewrite dec-true (j F.≟ j) ≡.refl | dec-true (j F.≟ j) ≡.refl = {!!}

    pivZsOfMatrix : VecPivotPosLeft (ys j) (pivZs j)
    pivZsOfMatrix = sameVecPiv (≡.sym ∘ isColXsYs j) vecPivXsZs

    pivZsJ≈pivMj : pivZs j ≈∙ pivsYs j
    pivZsJ≈pivMj = ≈∙-reflexive (alwaysSamePivot _ (pivZs j) (pivsYs j) pivZsOfMatrix (mPivsYs j))


  ... | ⊥₋ , _ | just p , _ | tri≈ ¬pivI<pivL b ¬c = {!!}
  ... | ⊥₋ , _ | ⊥₋ , c | tri≈ ¬pivI<pivL b ¬c = subst (NormedTwoBeforeAfter′ (pivZs i) (pivZs j)) (≡.sym compareEq)
    (helper5 , helper4)
    where

    helper5 : pivZs i ≈∙ pivsYs i
    helper5 rewrite dec-false (i F.≟ j) (<⇒≢ i<j) = ≈∙-refl

    pivPos : VecPivotPos (xs j) (pivsXs j .proj₁) (pivsXs j .proj₂) → AllZeros (xs j)
    pivPos rewrite pivJEq = id

    all0YsI : AllZeros (ys j)
    all0YsI k rewrite isColXsYs j k = pivPos (mXsPivs _) _

    pivJ≈⊥ : pivsYs j ≈∙ ⊥₋
    pivJ≈⊥ = ≈∙-reflexive (alwaysSamePivot _ (pivsYs j) ⊥₋ (mPivsYs j) (lift all0YsI))

    pivPosJ : VecPivotPos (xs j) (pivsXs j .proj₁) (pivsXs j .proj₂) → AllZeros (xs j)
    pivPosJ rewrite pivJEq = id

    allZXs : AllZeros (xs j)
    allZXs p = pivPosJ (mXsPivs _) _

    pivI≈⊥ : proj₁ (findNonZeroLeft (xs j ∘ fm′m)) ≈∙ ⊥₋
    pivI≈⊥ = ≈∙-reflexive (alwaysSamePivot _ _ ⊥₋ (proj₂ (findNonZeroLeft _)) (lift λ _ → allZXs _))

    helper4 : pivZs j >′ pivsYs j
    helper4 rewrite dec-true (j F.≟ j) ≡.refl | dec-true (j F.≟ j) ≡.refl | pivIEq =
      inj₂ (pivJ≈⊥ , pivI≈⊥)

  ... | just x , _ | _ | tri≈ ¬pivI<pivL b ¬c =
    contradiction helper2 ¬pivI<pivL
    where


    helper3 : pivsXs i .proj₁ <′ pivsXs j .proj₁
    helper3 = allRowsNormedRight _ _ i<j

    helper2 : pivsYs i <⁺ pivsYs j
    helper2 with helper3
    ... | inj₁ x = {!!}
    ... | inj₂ y = {!y!}

    pivZsJ≈pivMj : pivZs j >′ pivsYs j
    pivZsJ≈pivMj rewrite dec-true (j F.≟ j) ≡.refl = {!!}

  ... | _ | _ | tri> _ _ Pi>Pj = contradiction pivs≤ (<⁺→¬≥⁺ Pi>Pj)

subMatrixIsNormalized : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (fm′m : Fin m′ → Fin m)
  (pivsMatrix : Matrix F n m′) (isColMatrix : ColumnsFinOfMatrix xs fm′m pivsMatrix)
  (pivsOfPivMatrix : Vector (Fin m′ ⁺) n)
  (mPivsOfPivMatrix : MatrixPivotsLeft pivsMatrix pivsOfPivMatrix)
  (i j : Fin n) (i<j : i < j) (pivs≤ : pivsOfPivMatrix i ≤⁺ pivsOfPivMatrix j)
  (let ysPMpivs = pivsSubMatrix xs pivsXs pivsOfPivMatrix fm′m i j)
  → BothRowsAreNormalize i j (<⇒≢ i<j) pivsOfPivMatrix ysPMpivs
subMatrixIsNormalized xs pivsXs mXsPivs allRowsNormedRight fm′m pivsMatrix isColMatrix pivsOfPivMatrix mPivsOfPivMatrix i j i<j pivs≤
  = subMatrixDiffIndices xs pivsXs fm′m pivsOfPivMatrix i j ,
  subMatrixNormedBeforeAfter xs pivsXs mXsPivs allRowsNormedRight fm′m pivsMatrix isColMatrix pivsOfPivMatrix mPivsOfPivMatrix i j i<j pivs≤

normMatrixTwoRowsWithResult : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)

  (m′≤m : m′ ℕ.≤ m) (fm′m : Fin m′ → Fin m)
  (pivsMatrix : Matrix F n m′) (isColMatrix : ColumnsFinOfMatrix xs fm′m pivsMatrix)
  (pivsOfPivMatrix : Vector (Fin m′ ⁺) n)
  (mPivsOfPivMatrix : MatrixPivotsLeft pivsMatrix pivsOfPivMatrix)
  (i j : Fin n) (i<j : i < j) (pivs≤ : pivsOfPivMatrix i ≤⁺ pivsOfPivMatrix j)
  → Σ[ ys ∈ Matrix F n m ] Σ[ ysPM ∈ Matrix F n m′ ] Σ[ ysPMpivs ∈ Vector (Fin m′ ⁺) n ]
    MatrixPivots ys pivsXs × Maybe≈0 (ys j) (pivs i) × xs ≈ⱽ ys
      × MatrixPivotsLeft ysPM ysPMpivs × BothRowsAreNormalize i j (<⇒≢ i<j) pivsOfPivMatrix ysPMpivs
normMatrixTwoRowsWithResult {n = n} xs pivsXs mXsPivs allRowsNormedRight m′≤m fm′m pivsMatrix isColMatrix
  pivsOfPivMatrix mPivsOfPivMatrix i j i<j pivs≤ =
  ys , zs , pivZs , mPivotsYsPivs , maybe≈YsPiv , xs≈ⱽys , pivZsProof , normed

  where
  mPivotsYsPivs = normMatrixTwoRowsPivots xs pivsXs mXsPivs allRowsNormedRight i j i<j
  maybe≈YsPiv = normMatrixTwoRowsMaybe xs pivsXs mXsPivs allRowsNormedRight i j i<j
  xs≈ⱽys = normMatrixTwoRows≈ⱽ xs pivsXs i j i<j
  ys    = normMatrixTwoRowsF xs pivsXs i j
  zs    = subMatrix xs pivsXs fm′m i j
  pivZs = pivsSubMatrix xs pivsXs pivsOfPivMatrix fm′m i j
  pivZsProof = normMatrixTwoRowsMPivots xs pivsXs fm′m _ isColMatrix _ mPivsOfPivMatrix i j
  normed = subMatrixIsNormalized xs pivsXs mXsPivs allRowsNormedRight fm′m pivsMatrix isColMatrix pivsOfPivMatrix mPivsOfPivMatrix i j i<j pivs≤
