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
open import Data.Maybe as Maybe using (Maybe; maybe′; just; is-just; to-witness-T)
open import Data.Maybe.Relation.Binary.Pointwise as Maybe using ()
open import Data.Maybe.Relation.Unary.All as Maybe using ()
open import Data.Nat as ℕ using (ℕ; zero; suc; s<s)
open import Data.Nat.Properties as ℕ using (≰⇒>)
open import Data.List as L using (List; applyDownFrom)
import Data.List.Properties as L
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Linked.Properties
open import Data.List.Relation.Unary.AllPairs as AP using (AllPairs)
open import Data.List.Relation.Unary.AllPairs.Properties as AP
open import Relation.Binary.Construct.Add.Infimum.NonStrict
open import Data.Fin.Base as F hiding (_+_; _-_; lift; zero; suc)
open import Data.Fin.Patterns
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Sum
open import Data.Vec.Functional as V
open import Data.Vec.Functional.Properties
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as EqSetoids
open import Algebra
import Algebra.Properties.Ring as RingProps
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; _≗_; refl; subst)
open import Relation.Binary.Construct.Add.Infimum.Strict hiding (_<₋_)
import Relation.Binary.Construct.Add.Point.Equality as Equality
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Unary as RU using (Pred)
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
open import Vector.SubVector
open import AllPairs.Properties
open import Algebra.Matrix
open import Algebra.MatrixData renaming (Matrix to MatrixData)
import Algebra.HeytingField.Properties as HFProps
import MatrixFuncNormalization.MatrixProps as MatrixPropsBefore
import MatrixFuncNormalization.MatrixPropsAfter as MatrixPropsAfter
import MatrixFuncNormalization.normBef as NormBef
import MatrixFuncNormalization.NormAfter.Base as NormAfterBase
open import MatrixFuncNormalization.NormAfter.FinInduction
open import MatrixNormalization.FinProps
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
open import Algebra.Module.Base ring
open M hiding (_+ᴹ_)
open module PVec {n} = VecSpace (leftModule n)
open module PNormBef {n} = MatrixPropsBefore (<-strictTotalOrder n) using (NormedTwoBeforeAfter; compare⊤⁺)
open PNormBef using (NormedTwoBeforeAfter; NormedTwoBeforeAfter′; compare⊤⁺; _>′_)
open PNormAfter using (_<′_; AllRowsNormalizedRight; simpleFinProps)
open HCRProps heytingCommutativeRing
open RingProps ring
module ≈ = Setoid setoid
open ≋‵ using (≋-setoid)
open module ≋ {n} = EqSetoids (≋-setoid n)
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
  A B : Set ℓ
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

maybeSameness : ∀ {xs ys : Vector F n} p → xs ≋‵.≋ ys → Maybe≈0 xs p → Maybe≈0 ys p
maybeSameness (just _) ys≈xs = ≈.trans (≈.sym (ys≈xs _))
maybeSameness ⊥₋ _ _ = _

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
normTwoRowsPropsVecPiv {xs = xs} {ys} {px′@(just px)} {py′@(just py)} {vx′@(vx , vx#0)}
  {_ , vy#0} (vx≈xsPx , fxs) (vy≈ysPy , fys) _≤₋_.[ px<py ] =
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
  (vx≈xsPx , fxs) (vy≈ysPy , fys) (_≤₋_.[ _ ]) =

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

crescentPiv : ∀ (xs : Vector F n) (p : Fin n) piv piv#0
  (columns : Vector (Fin n) m) (ys : Vector F m) j
  → Lookup≢0 xs p piv piv#0
  → columns j ≡ p
  → Monotone columns → SubVector xs columns ys → Lookup≢0 ys j _ piv#0
crescentPiv xs p piv piv#0 columns ys j (piv≡xsP , isPiv) colJ≡p cresc (subProp subVecProp) .proj₁ =
  trans piv≡xsP (reflexive $ ≡.sym $ ≡.trans (subVecProp _) (≡.cong xs colJ≡p))
crescentPiv xs p piv piv#0 columns ys j (piv≡xsP , isPiv) colJ≡p cresc (subProp subVecProp) .proj₂ i i>j =
  trans (reflexive (subVecProp _)) (isPiv _ (ℕ.≤-<-trans (≤-reflexive (≡.sym colJ≡p)) (cresc i>j)))

-- Properties of Matrix

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
 normTwoRowsPropsVecPiv (mXsPivs _) (mXsPivs _) (allRowsNormedRight i<j)
normMatrixTwoRowsPropsVecPos xs pivsXs mXsPivs allRowsNormedRight i j i<j k false (ofⁿ _) = mXsPivs k

normMatrixTwoRowsPropsMaybe : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (let pivs = pivsWV→pivs pivsXs)
  (mXsPivs : MatrixPivots xs pivsXs) (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (i j : Fin n) (i<j : i < j) (k : Fin n) (ref : Reflects (k ≡ j) true) →
    let ys = normMatrixTwoRowsF′ xs pivsXs i j k true in
      Maybe≈0 ys (pivs i)
normMatrixTwoRowsPropsMaybe xs pivsXs mXsPivs allRowsNormedRight i j i<j _ (ofʸ ≡.refl) =
  normTwoRowsPropsMaybe (mXsPivs _) (mXsPivs _) (allRowsNormedRight i<j)

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

module _ (matrixStart : Matrix F (ℕ.suc n) m) (pivsStart : Vector (PivWithValue m) (ℕ.suc n))
  (mPivsStart : MatrixPivots matrixStart pivsStart)
  (allRowsNormedRight : AllRowsNormalizedRight (pivsWV→pivs pivsStart))
  where

  MatrixFromStart : Set _
  MatrixFromStart = Σ[ xs ∈ Matrix F (ℕ.suc n) m ] (matrixStart ≈ⱽ xs × MatrixPivots xs pivsStart)

  private
    RemainSame : (i : Fin (ℕ.suc n)) (xs ys : Matrix F (ℕ.suc n) m) → Set _
    RemainSame i xs ys = ∀ k → k ≢ i → xs k ≗ ys k

  Pij′ : (i j : Fin (ℕ.suc n)) .(i≤j : i ≤ j) (xs : MatrixFromStart) → Set ℓ₁
  Pij′ i j i≤j (xs , _ , _) =
    (∀ k p → k < i → k < p → Maybe≈0 (xs p) (pivsStart k .proj₁)) × (∀ k → i < k → k ≤ j → Maybe≈0 (xs k) (pivsStart i .proj₁))

  Pi′ : (i : Fin (ℕ.suc n)) (xs : MatrixFromStart) → Set ℓ₁
  Pi′ i (xs , _ , _) = ∀ k p → k ≤ i → k < p → Maybe≈0 (xs p) (pivsStart k .proj₁)

  P′ : (xs : MatrixFromStart) → Set ℓ₁
  P′ (xs , _ , _) = ∀ i j → i < j → Maybe≈0 (xs j) (pivsStart i .proj₁)


  Pab′ : (i j : Fin (ℕ.suc n)) .(i≢j : i ≢ j) (xs ys : MatrixFromStart) → Set _
  Pab′ i j _ (xs , mStart≈ⱽxs , mpivsXs) (ys , mStart≈ⱽys , mpivsYs) =
    Maybe≈0 (ys j) (pivsStart i .proj₁) × RemainSame j xs ys × ∀ k → xs i k ≈ 0# → ys j k ≈ xs j k

  P00′ : (xs : MatrixFromStart) → Pij′ F.zero F.zero ℕ.z≤n xs
  proj₁ (P00′ _) _ _ ()
  proj₂ (P00′ _) 0F () ℕ.z≤n
  proj₂ (P00′ _) (Fin.suc k) _ ()

  Pij→Pi′ : ∀ (i : Fin (ℕ.suc n)) xs (pij : Pij′ i (fromℕ _) (≤fromℕ _) xs) → Pi′ i xs
  Pij→Pi′ i (xs , mStart≈ⱽxs , mpivsXs) (bef , after) k p k≤i k<p with k F.≟ i
  ... | no k≢i = bef _ _ (≤∧≢⇒< k≤i k≢i) k<p
  ... | yes ≡.refl = after _ k<p (≤fromℕ _)

  Pi→P′ : ∀ xs (pi : Pi′ (fromℕ n) xs) → P′ xs
  Pi→P′ (xs , mStart≈ⱽxs , mpivsXs) pi i j i<j = pi _ _ (≤fromℕ _) i<j

  Pi→Pii′ : ∀ (i : Fin n) xs (pi : Pi′ (inject₁ i) xs) → Pij′ (F.suc i) (F.suc i) F.≤-refl xs
  proj₁ (Pi→Pii′ i (xs , mStart≈ⱽxs , mpivsXs) pi) k p (ℕ.s≤s k≤i) k<p = pi _ _ (cong≤ˡ k≤i (≡.sym (toℕ-inject₁ _))) k<p
  proj₂ (Pi→Pii′ i (xs , mStart≈ⱽxs , mpivsXs) pi) k si<k k<si = contradiction (ℕ.≤-<-trans k<si si<k) ℕ.1+n≰n

  Ps′ : ∀ i (j : Fin n) .(i≤j : i ≤ j) xs ys
    (pij : Pij′ i (inject₁ j) (cong≤ʳ (≡.sym (toℕ-inject₁ _)) i≤j) xs)
    (pab : Pab′ i (F.suc j) (F.<⇒≢ (ℕ.s≤s i≤j)) xs ys)
    → Pij′ i (F.suc j) (ℕ.m≤n⇒m≤1+n i≤j) ys
  proj₁ (Ps′ i j i≤j (xs , _) (ys , _) (bef , after) (maybe , sameness , 0NotMod)) k p k<i k<p with p F.≟ F.suc j
  ... | no p≢sj = maybeSameness (pivsStart k .proj₁) (reflexive ∘ sameness _ p≢sj) (bef _ _ k<i k<p)
  ... | yes ≡.refl with pivsStart k .proj₁ in eq
  ... | just pivK = let befN = subst (Maybe≈0 (xs i)) eq (bef k i k<i k<i) in ≈.trans (0NotMod _ befN)
    let afterN = bef k (F.suc j) k<i k<p in subst (Maybe≈0 (xs (Fin.suc j))) eq afterN
  ... | ⊥₋ = _
  proj₂ (Ps′ i j i≤j (xs , _) (ys , _) (bef , after) (maybe , sameness , 0NotMod)) k i<k k<j with k F.≟ F.suc j
  ... | no k≢sj = maybeSameness (pivsStart i .proj₁) (reflexive ∘ sameness _ k≢sj)
    (after _ i<k (ℕ.≤-pred (ℕ.≤∧≢⇒< (cong≤ʳ (≡.cong suc (≡.sym (toℕ-inject₁ _))) k<j)
    λ k≡s₁j → k≢sj (toℕ-injective (≡.trans k≡s₁j (≡.cong suc (toℕ-inject₁ _)))))))
  ... | yes ≡.refl = maybe

  open FinProps

  propsMatrix : FinProps MatrixFromStart n
  Pij propsMatrix = Pij′
  Pi propsMatrix = Pi′
  P propsMatrix = P′
  Pab propsMatrix = Pab′
  Pij→Pi propsMatrix = Pij→Pi′
  Pi→P propsMatrix = Pi→P′
  Pi→Pii propsMatrix = Pi→Pii′
  Ps propsMatrix = Ps′
  P00 propsMatrix = P00′


  getNextMat : ∀ i j i<j → Op₁ MatrixFromStart
  getNextMat i j i<j (xs , mStart≈xs , mPivs) = normMatrixTwoRowsF xs pivsStart i j ,
    ≈ⱽ-trans mStart≈xs (normMatrixTwoRows≈ⱽ _ _ _ _ i<j) , normMatrixTwoRowsPivots _ _ mPivs allRowsNormedRight _ _ i<j

  pab : ∀ i j i<j xs → Pab′ i j (<⇒≢ i<j) xs (getNextMat i j i<j xs)
  proj₁ (pab i j i<j (xs , mStart≈xs , mPivs)) = normMatrixTwoRowsMaybe xs pivsStart mPivs allRowsNormedRight _ j i<j
  proj₁ (proj₂ (pab i j i<j (xs , mStart≈xs , mPivs))) k k≢j p
    rewrite dec-no (k F.≟ j) k≢j = ≡.refl
  proj₂ (proj₂ (pab i j i<j (xs , mStart≈xs , mPivs))) k xsIk≈0
    rewrite dec-yes (j F.≟ j) ≡.refl .proj₂ = helper
    where
    open ≈-Reasoning

    helper : normTwoRows (xs i) (xs j) (pivsStart i .proj₁) (pivsStart j .proj₁) (pivsStart i .proj₂) k HF.≈ xs j k
    helper with pivsStart i  in eq
    ... | ⊥₋ , _ = ≈.refl
    ... | just piv , pInv = begin
      xs j k + _ * xs i k ≈⟨ +-congˡ (*-congˡ xsIk≈0) ⟩
      xs j k + _ * 0#     ≈⟨ +-congˡ (zeroʳ _) ⟩
      xs j k + 0#         ≈⟨ +-identityʳ _ ⟩
      xs j k ∎


  open ToInduct

  ind : ToInduct MatrixFromStart n
  f ind = getNextMat
  finProps ind = propsMatrix
  fPab ind = pab

  normMatrix : MatrixFromStart → Σ MatrixFromStart P′
  normMatrix = getProperty ind


AllRowsNormalizedLeft′ : Matrix F (ℕ.suc n) m → Vector (Fin m ₋) (ℕ.suc n) → Set _
AllRowsNormalizedLeft′ xs pivs = ∀ i j → i ≢ j → Maybe≈0 (xs j) $ pivs i

ColumnsZero : Matrix F n m → Vector (Fin m ₋) n → Set _
ColumnsZero xs pivs = ∀ i j → i ≢ j → Maybe≈0 (xs j) $ pivs i

AllRowsNormalizedLeft : Matrix F (ℕ.suc n) m → Vector (PivWithValue m) (ℕ.suc n) → Set _
AllRowsNormalizedLeft xs pivs = ∀ i j → i ≢ j → Maybe≈0 (xs j) $ pivs i .proj₁

AllRowsNormalizedLeftBelow : Matrix F (ℕ.suc n) m → Vector (PivWithValue m) (ℕ.suc n) → Set _
AllRowsNormalizedLeftBelow xs pivs = ∀ i j → i < j → Maybe≈0 (xs j) (pivs i .proj₁)

-- Matrix with the properties

module _ (xs : Matrix F (ℕ.suc n) m) (pivsWithValue : Vector (PivWithValue m) (ℕ.suc n))
  (matrixPivots : MatrixPivots xs pivsWithValue)
  (let pivs = pivsWV→pivs pivsWithValue)
  (allRowsNormedRight : AllRowsNormalizedRight pivs)
  (allNormedLeftBelow : AllRowsNormalizedLeftBelow xs pivsWithValue)
  where

  allNormedLeft : AllRowsNormalizedLeft xs pivsWithValue
  allNormedLeft i j i≢j with <-cmp i j
  ... | tri< i<j _ _ = allNormedLeftBelow _ _ i<j
  ... | tri≈ _ i≡j _ = contradiction i≡j i≢j
  ... | tri> _ _ i>j with pivsWithValue i in eq
  ... | ⊥₋ , _  = _
  ... | just p , _ , _  with pivsWithValue j in eqJ
  ... | ⊥₋ , _ = helper (matrixPivots j)
    where
    helper : VecPivotPos (xs j) (pivsWithValue j .proj₁) (pivsWithValue j .proj₂) → xs j p ≈ 0#
    helper w rewrite eqJ = helper2 w where
      helper2 : _ → _
      helper2 allZ = allZ _

  ... | just v , _ , _ = helper (matrixPivots j)
    where
    helper : VecPivotPos (xs j) (pivsWithValue j .proj₁) (pivsWithValue j .proj₂) → xs j p ≈ 0#
    helper w rewrite eqJ = helper2 w where
      helper2 : _ → _
      helper2 (_ , eqZ) = eqZ _ (helper3 (allRowsNormedRight i>j)) where
        helper3 : proj₁ (pivsWithValue j) <′ proj₁ (pivsWithValue i) → p > v
        helper3 w2 rewrite eq | eqJ = helper4 w2 where
          helper4 : _ → _
          helper4 _≤₋_.[ v<p ] = v<p
