open import Algebra.DecidableField

module MatrixFuncNormalization.ElimZeros.Properties {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level using (Level; lift)
open import Algebra
open import Algebra.Apartness
open import Function
open import Data.Product
open import Data.Fin as F using (Fin; zero; suc; inject!; toℕ)
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.Maybe
open import Data.Sum
open import Data.Nat using (ℕ; NonZero; z≤n; s<s)
open import Data.Vec.Functional as V
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
open import Relation.Nullary.Construct.Add.Supremum
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong)
open import Relation.Binary.Construct.Add.Supremum.Strict

open import Algebra.Matrix
open import MatrixFuncNormalization.normBef dField using (VecPivotPos; MatrixPivots)
open import MatrixFuncNormalization.ElimZeros.Base dField hiding (divideVec)
open import MatrixFuncNormalization.NormAfter.Properties dField using (ColumnsZero; Maybe≈0)
open import MatrixFuncNormalization.NormAfter.PropsFlip dField
open import MatrixFuncNormalization.Definitions dField

open DecidableField dField renaming (Carrier to F; heytingField to hField) hiding (sym)
open HeytingField hField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (ring; sym)
open import Algebra.HeytingField.Properties hField
open import Algebra.Ring.Properties
import Algebra.Module.Definition as MDefinition
import Algebra.Module.PropsField as PField
open import Algebra.Module.Instances.FunctionalVector ring
open import Algebra.BigOps

open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.Reasoning.Setoid setoid
open Units ring
open module PFieldN {n} = PField dField (leftModule n)
open module MDefN {n} = MDefinition (leftModule n)
open PNorm
open module ∑′ {n} = SumCommMonoid (commutativeMonoid n)

private variable
  m n : ℕ

invVecValue : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → F
invVecValue xs ⊤⁺ vPos = 1#
invVecValue xs [ p ] (xp#0 , _) = proj₁ (#0⇒invertible xp#0)

divideVec : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec xs ⊤⁺ vPos i = xs i
divideVec xs [ p ] (xp#0 , _) i = #⇒invertible xp#0 .proj₁ * xs i

divideVec₂ : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → Vector F n
divideVec₂ xs p vPos i = invVecValue xs p vPos * xs i

dV₂≈dV : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → divideVec₂ xs p vPos ≋ divideVec xs p vPos
dV₂≈dV xs ⊤⁺ vPos _ = *-identityˡ _
dV₂≈dV xs [ p ] vPos i = refl

divideVecPreservesPos : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → VecPivotPos (divideVec xs p vPos) p
divideVecPreservesPos xs ⊤⁺ vPos = vPos
proj₁ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) = x#0y#0→xy#0 (x⁻¹#0 _ _) xp#0
proj₂ (divideVecPreservesPos xs [ p ] vPos@(xp#0 , xi≈0)) i i<p = begin
  _ * xs i ≈⟨ *-congˡ (xi≈0 i i<p) ⟩
  _ * 0#   ≈⟨ zeroʳ _ ⟩
  0# ∎

divideVec≈0 : ∀ {xs : Vector F n} {q} (vPos : VecPivotPos xs q) p → xs p ≈ 0# → divideVec xs q vPos p ≈ 0#
divideVec≈0 {q = [ q ]} vPos p xsP≈0 = trans (*-congˡ xsP≈0) (0RightAnnihilates _)
divideVec≈0 {q = ⊤⁺} vPos p = id

divideVecP≈1 : ∀ {xs : Vector F n} {p} (vPos : VecPivotPos xs p) → All (λ i → divideVec xs p vPos i ≈ 1#) p
divideVecP≈1 {xs = xs} {[ i ]} (xsI#0 , _) = let x⁻¹ = #⇒invertible xsI#0 .proj₁ in just (begin
  x⁻¹ * xs i       ≈˘⟨ *-congˡ (trans (+-congˡ -0#≈0#) (+-identityʳ _)) ⟩
  x⁻¹ * (xs i - 0#) ≈⟨ #⇒invertible xsI#0 .proj₂ .proj₁ ⟩
  1# ∎)
divideVecP≈1 {p = ⊤⁺} vPos = nothing

invVecValue#0 : ∀ (xs : Vector F n) p (vPos : VecPivotPos xs p) → invVecValue xs p vPos # 0#
invVecValue#0 xs ⊤⁺ vPos = 1#0
invVecValue#0 xs [ p ] vPos = x⁻¹#0 _ _

firstZero : Vector (Fin m ⁺) n → Fin (ℕ.suc n)
firstZero {n = ℕ.zero} xs = 0F
firstZero {n = ℕ.suc n} xs = maybe′ (const (suc (firstZero (tail xs)))) 0F (xs 0F)

normPivs : ∀ (pivs : Vector (Fin m ⁺) n) → Vector (Fin m) (toℕ (firstZero pivs))
normPivs {n = ℕ.suc n} pivs i with pivs 0F
normPivs {n = ℕ.suc n} pivs 0F | just i = i
normPivs {n = ℕ.suc n} pivs (suc i) | just _ = normPivs (tail pivs) i

mPivs≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs)
  → MatrixPivots≁0 (xs ∘ inject!) (normPivs pivs)
mPivs≁0′ {n = ℕ.suc n} xs pivs mPivs i with pivs 0F | mPivs 0F
mPivs≁0′ {_} {ℕ.suc n} xs pivs mPivs 0F | just x | c  = c
mPivs≁0′ {_} {ℕ.suc n} xs pivs mPivs (suc i) | just x | _ = mPivs≁0′ (tail xs) (tail pivs) (mPivs ∘ suc) i

normPivsSame : ∀ (pivs : Vector (Fin m ⁺) n) i → just (normPivs pivs i) ≡ pivs (inject! i)
normPivsSame {n = ℕ.suc n} pivs i with pivs 0F in eq
normPivsSame {n = ℕ.suc n} pivs 0F | just x rewrite eq = ≡.refl
normPivsSame {n = ℕ.suc n} pivs (suc i) | just x rewrite eq = normPivsSame {n = n} (tail pivs) i

private
  injectPreserves : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → i F.< j → inject! i F.< inject! j
  injectPreserves {ℕ.suc n} {k = suc k} {0F} {suc j} (s<s z≤n) = s<s z≤n
  injectPreserves {ℕ.suc n} {k = suc k} {suc i} {suc j} (s<s i<j) = s<s (injectPreserves i<j)

  inject⇒≡ : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → inject! i ≡ inject! j → i ≡ j
  inject⇒≡ {ℕ.zero} {0F} {i = ()} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = 0F} {0F} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = 0F} {suc j} x
  inject⇒≡ {ℕ.zero} {suc ()} {i = suc i} x
  inject⇒≡ {ℕ.suc n} {suc k} {0F} {0F} ≡.refl = ≡.refl
  inject⇒≡ {ℕ.suc n} {suc k} {suc i} {suc j} eq rewrite inject⇒≡ (suc-injective eq) = ≡.refl

  inject⇒≢ : ∀ {k : Fin (ℕ.suc n)} {i j : F.Fin′ k} → i ≢ j → inject! i ≢ inject! j
  inject⇒≢ = _∘ inject⇒≡

pivsCrescent≁0′ : {pivs : Vector (Fin m ⁺) n} (normed : AllRowsNormalized pivs) → AllRowsNormalized≁0 (normPivs pivs)
pivsCrescent≁0′ {pivs = pivs} normed {i} {j} i<j = helper $ normed _ _ $ injectPreserves i<j
  where
  helper2 : _ → _
  helper2 (inj₁ [ pI<pJ ]) = pI<pJ

  helper : pivs (inject! i) <′ pivs (inject! j) → _
  helper rewrite ≡.sym (normPivsSame pivs i) | ≡.sym (normPivsSame pivs j) = helper2

cols0≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (cols0 : ColumnsZero xs pivs)
  → ColumnsZero≁0 (xs ∘ inject!) (normPivs pivs)
cols0≁0′ {n = ℕ.suc n} xs pivs cols0 i j i≢j = helper $ cols0 _ _ $ inject⇒≢ i≢j
  where
  helper : Maybe≈0 (xs (inject! j)) (pivs (inject! i)) → _
  helper rewrite ≡.sym (normPivsSame pivs i) = id

pivsOne≁0′ : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (pivsOne : PivsOne xs pivs)
  → PivsOne≁0 (xs ∘ inject!) (normPivs pivs)
pivsOne≁0′ {n = ℕ.suc n} xs pivs pivsOne i with pivs 0F | pivsOne 0F
pivsOne≁0′ {_} {ℕ.suc n} xs pivs pivsOne 0F | just a | just b = b
pivsOne≁0′ {_} {ℕ.suc n} xs pivs pivsOne (suc i) | just a | just b = pivsOne≁0′ (tail xs) (tail pivs) (pivsOne ∘ F.suc) i

eq0Piv : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → firstZero pivs ≡ 0F → ∀ i
  → xs i ≋ 0ᴹ
eq0Piv {n = ℕ.suc n} xs pivs mPivs normed fP≈0 0F j with pivs 0F | mPivs 0F
... | ⊤⁺ | lift lower = lower _
eq0Piv {n = ℕ.suc n} xs pivs mPivs normed fP≈0 (suc i) j with pivs 0F | pivs (suc i) | normed 0F (suc i) (s<s z≤n) |  mPivs (suc i)
... | ⊤⁺ | ⊤⁺ | inj₂ _ | lift lower = lower _


sumZero : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → firstZero pivs ≡ 0F
  → ∑ xs ≈ᴹ 0ᴹ
sumZero {n = n} xs pivs mPivs normed fZ i = begin
  ∑ xs i ≈⟨ ∑Ext (eq0Piv xs pivs mPivs normed fZ) i ⟩
  ∑ {_} {n} (const (const 0#)) i ≈⟨ ∑0r n _ ⟩
  0# ∎

injSuc : ∀ {c : Fin (ℕ.suc n)} i → inject! {i = suc c} (suc i) ≡ F.suc (inject! {i = c} i)
injSuc i = ≡.refl

∑Inj′ : ∀ (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs) {c}
  → firstZero pivs ≡ c
  → ∑ (xs ∘ inject! {i = c}) ≈ᴹ ∑ xs
∑Inj′ xs pivs mPivs normed {0F} eqn i = sym $ sumZero xs pivs mPivs normed eqn i
∑Inj′ {n = ℕ.suc n} xs pivs mPivs normed {suc c} eqn i  with pivs 0F
... | just _ = begin
  xs 0F i + ∑ {_} {toℕ c} (xs ∘ suc ∘ inject! {i = c}) i ≈⟨ +-congˡ
    (∑Inj′ (tail xs) (tail pivs) (mPivs ∘ suc) (λ a b a<b → normed (suc a) (suc b) (s<s a<b)) {c} (suc-injective eqn) i) ⟩
  xs 0F i + ∑ {_} {n} (xs ∘ suc) i ∎

∑Inj : ∀ {xs : Matrix F _ m} {pivs : Vector (Fin m ⁺) n} (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → ∑ (xs ∘ inject! {i = firstZero pivs}) ≈ᴹ ∑ xs
∑Inj mPivs normed = ∑Inj′ _ _ mPivs normed ≡.refl

sumZero′ : (xs : Matrix F _ m) (ys : Vector F n) (pivs : Vector (Fin m ⁺) n)
  (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → firstZero pivs ≡ 0F
  → ∑ (ys *ᵣ xs) ≈ᴹ 0ᴹ
sumZero′ {n = n} xs ys pivs mPivs normed eqn i = begin
  ∑ (ys *ᵣ xs) i ≈⟨ ∑Ext (λ j k → trans (*-congˡ (eq0Piv xs pivs mPivs normed eqn j k)) (zeroʳ _)) i ⟩
  ∑ {_} {n} (const $ const 0#) i ≈⟨ ∑0r n _ ⟩
  0# ∎

∑Inj′₂ : ∀ (xs : Matrix F _ m) (ys : Vector F n) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs)
  (normed : AllRowsNormalized pivs) {c}
  → firstZero pivs ≡ c
  → ∑ ((ys *ᵣ xs) ∘ inject! {i = c}) ≈ᴹ ∑ (ys *ᵣ xs)
∑Inj′₂ xs ys pivs mPivs normed {0F} eq i = sym (sumZero′ xs ys pivs mPivs normed eq i)
∑Inj′₂ {n = ℕ.suc n} xs ys pivs mPivs normed {suc c} eq i with pivs 0F
... | just x = +-congˡ (∑Inj′₂ (tail xs) (tail ys) (tail pivs) (mPivs ∘ suc) (λ a b a<b → normed _ _ (s<s a<b)) (suc-injective eq) i)

∑Inj₂ : ∀ {xs : Matrix F _ m} {pivs : Vector (Fin m ⁺) n} (ys : Vector F n) (mPivs : MatrixPivots xs pivs)
  (normed : AllRowsNormalized pivs)
  → ∑ ((ys *ᵣ xs) ∘ inject! {i = firstZero pivs}) ≈ᴹ ∑ (ys *ᵣ xs)
∑Inj₂ ys mPivs normed = ∑Inj′₂ _ ys _ mPivs normed ≡.refl

open _reaches_ renaming (ys to ws; xs*ys≈x to xs*ws≈x)

xs⊆ⱽxs∘inj : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → xs ⊆ⱽ xs ∘ inject! {i = firstZero pivs}
ws (xs⊆ⱽxs∘inj xs pivs mPivs normed (ys by xs*ys≈x)) = ys ∘ inject!
xs*ws≈x (xs⊆ⱽxs∘inj xs pivs mPivs normed {x} (ys by xs*ys≈x)) i = begin
  ∑ ((ys *ᵣ xs) ∘ inject! {i = firstZero pivs}) i ≈⟨ ∑Inj₂ ys mPivs normed i ⟩
  ∑ (ys *ᵣ xs) i                                  ≈⟨ xs*ys≈x i ⟩
  x i ∎

vecInj : (k : Fin (ℕ.suc n)) (ys : Vector F $ toℕ $ k) → Vector F n
vecInj 0F ys i = 0#
vecInj (suc k) ys 0F = ys 0F
vecInj (suc k) ys (suc i) = vecInj k (tail ys) i

vecInjProp : ∀ (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (ys : Vector F _)
  (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs) c
  → firstZero pivs ≡ c
  → ∑ (vecInj (firstZero pivs) ys *ᵣ xs) ≈ᴹ ∑ (ys *ᵣ xs ∘ inject!)
vecInjProp {n = ℕ.zero} xs pivs ys mPivs normed 0F eqn i = refl
vecInjProp {n = ℕ.suc n} xs pivs ys mPivs normed 0F eqn i with pivs 0F
... | ⊤⁺ = begin
  0# * _ + ∑ {_} {n} (λ _ _ → 0# * _) i ≈⟨ +-cong (zeroˡ _) (trans (∑Ext {_} {n} (λ j k → zeroˡ _) i) (∑0r n i)) ⟩
  0# + 0# ≈⟨ +-identityˡ _ ⟩
  0# ∎
vecInjProp {n = ℕ.suc n} xs pivs ys mPivs normed (suc c) eqn i with pivs 0F
... | just x = +-congˡ $ vecInjProp (tail xs) (tail pivs) (tail ys) (mPivs ∘ suc) (λ a b a<b → normed _ _ (s<s a<b))
  c (suc-injective eqn) i

xs⊇ⱽxs∘inj : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → xs ⊇ⱽ xs ∘ inject! {i = firstZero pivs}
ws (xs⊇ⱽxs∘inj {n = n} xs pivs mPivs normed (ys by xs*ys≈x)) = vecInj (firstZero pivs) ys
xs*ws≈x (xs⊇ⱽxs∘inj {n = n} xs pivs mPivs normed {x} (ys by xs*ys≈x)) i = begin
  ∑ (vecInj (firstZero pivs) ys *ᵣ xs) i ≈⟨ vecInjProp xs pivs ys mPivs normed _ ≡.refl i ⟩
  ∑ (ys *ᵣ xs ∘ inject!) i               ≈⟨ xs*ys≈x i ⟩
  x i ∎

xs≋ⱽxs∘inj : (xs : Matrix F _ m) (pivs : Vector (Fin m ⁺) n) (mPivs : MatrixPivots xs pivs) (normed : AllRowsNormalized pivs)
  → xs ≋ⱽ xs ∘ inject! {i = firstZero pivs}
xs≋ⱽxs∘inj xs pivs mPivs normed = record
  { fwd = xs⊆ⱽxs∘inj xs pivs mPivs normed
  ; bwd = xs⊇ⱽxs∘inj xs pivs mPivs normed
  }

module MatNormed (xsNormed : MatrixNormed m n) where

  open MatrixNormed xsNormed

  ys : Matrix F n m
  ys i = divideVec (xs i) (pivs i) (mPivots i)

  mPivAfter : MatrixPivots ys pivs
  mPivAfter _ = divideVecPreservesPos _ _ _

  columnsZeros : ColumnsZero ys pivs
  columnsZeros i j i≢j = helper (columnsZero i j i≢j)
    where
    helper : Maybe≈0 (xs j) (pivs i) → Maybe≈0 (divideVec (xs j) (pivs j) (mPivots j)) (pivs i)
    helper with pivs i
    ... | ⊤⁺  = λ _ → _
    ... | [ p ]  = divideVec≈0 (mPivots j) p

  pivsOne : PivsOne ys pivs
  pivsOne _ = divideVecP≈1 _

  xs≋ⱽys : xs ≋ⱽ ys
  xs≋ⱽys = ≋ⱽ-trans (*#0≈ⱽ xs λ i → invVecValue#0 (xs i) (pivs i) (mPivots i))
    (≋⇒≋ⱽ λ i → dV₂≈dV (xs i) (pivs i) (mPivots i))

  ysNormed : MatrixIsNormed ys
  ysNormed = record
    { mPivots = mPivAfter
    ; pivsCrescent = pivsCrescent
    ; columnsZero = columnsZeros
    }

  ysIsNormed≈1 : MatrixIsNormed≈1 ys
  ysIsNormed≈1 = record { isNormed = ysNormed ; pivsOne = pivsOne }

  ysNormed≈1 : MatrixNormed≈1 m n
  ysNormed≈1 = record { isNormed≈1 = ysIsNormed≈1 }

  sizeF = firstZero pivs
  n′ = toℕ sizeF

  xs≁0 : Matrix F n′ m
  xs≁0 = xs ∘ inject! {i = sizeF}
  pivs≁0 = normPivs pivs

  mPivs≁0 : MatrixPivots≁0 xs≁0 pivs≁0
  mPivs≁0 = mPivs≁0′ xs pivs mPivots

  pivsCrescent≁0 : AllRowsNormalized≁0 pivs≁0
  pivsCrescent≁0 x<y = pivsCrescent≁0′ pivsCrescent x<y

  colsZero : ColumnsZero≁0 xs≁0 pivs≁0
  colsZero = cols0≁0′ _ _ columnsZero

  pivsOne≁0 : PivsOne xs pivs → PivsOne≁0 xs≁0 pivs≁0
  pivsOne≁0 = pivsOne≁0′ _ _

  xs≋ⱽxs≁0 : xs ≋ⱽ xs≁0
  xs≋ⱽxs≁0 = xs≋ⱽxs∘inj xs pivs mPivots pivsCrescent

  xsIsNormed≁0 : MatrixIsNormed≁0 xs≁0
  xsIsNormed≁0 = record
    { mPivots = mPivs≁0
    ; pivsCrescent = pivsCrescent≁0
    ; columnsZero = colsZero
    }

  xsNormed≁0 : MatrixNormed≁0 _ _
  xsNormed≁0 = record { isNormed = xsIsNormed≁0 }

  module _ (pivsOne : PivsOne≁0 xs≁0 pivs≁0) where

    xs≁0≈1isNormed : MatrixIsNormed≁0≈1 xs≁0
    xs≁0≈1isNormed = record { isNormed = xsIsNormed≁0 ; pivsOne = pivsOne }

    xs≁0≈1Normed : MatrixNormed≁0≈1 _ _
    xs≁0≈1Normed = record { isNormed≈1 = xs≁0≈1isNormed }


module FromNormed (xsNormed : MatrixNormed m n) where

  open MatrixNormed xsNormed
  open MatNormed xsNormed public

  ysFromNormalization : FromNormalization≈1 xs
  ysFromNormalization = record
    { ysNormed = ysIsNormed≈1
    ; xs≋ⱽys   = xs≋ⱽys
    }

  xs≁0FromFormalization : FromNormalization≁0 xs _
  xs≁0FromFormalization = record
    { ysNormed = xsIsNormed≁0
    ; xs≋ⱽys   = xs≋ⱽxs≁0
    }

module FromNormed≈1 (xsNormed≈1 : MatrixNormed≈1 m n) where

  open MatrixNormed≈1 xsNormed≈1
  open FromNormed xsNormed hiding (pivsOne) public

  xs≁0Normed : MatrixIsNormed≁0≈1 xs≁0
  xs≁0Normed = xs≁0≈1isNormed (pivsOne≁0 pivsOne)

  xs≁0≈1FromFormalization : FromNormalization≁0≈1 xs _
  xs≁0≈1FromFormalization = record
    { ysNormed = xs≁0Normed
    ; xs≋ⱽys   = xs≋ⱽxs≁0
    }
