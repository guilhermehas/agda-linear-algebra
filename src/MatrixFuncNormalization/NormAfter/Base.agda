open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.NormAfter.Base {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Level using (Level; Lift; lift; _⊔_)
open import Function hiding (flip)
open import Data.Bool using (Bool; false; true; T)
open import Data.Unit renaming (⊤ to ⊤₂) using ()
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product
open import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Fin.Base hiding (_+_; lift)
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Vec.Functional as V
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as EqSetoids
open import Algebra
import Algebra.Properties.Ring as RingProps
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary.Decidable
open import Relation.Nullary.Construct.Add.Infimum as ₋
import Algebra.Module.Instances.FunctionalVector as AMIF
import Algebra.Apartness.Properties.HeytingCommutativeRing as HCRProps
open import Relation.Binary.PropositionalEquality as ≡ hiding (setoid)

open import Algebra.Matrix
open import Algebra.MatrixData renaming (Matrix to MatrixData)
import Algebra.HeytingField.Properties as HFProps
import MatrixFuncNormalization.MatrixProps as MatrixPropsBefore
import MatrixFuncNormalization.MatrixPropsAfter as MatrixPropsAfter
import MatrixFuncNormalization.normBef as NormBef
open import MatrixFuncNormalization.FinInduction
import Algebra.Module.VecSpace as VecSpace
open import Vector
open import lbry

open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open NormBef hField _≟_ using (normalizeMatrix; AllZeros; _-v_)
  renaming ( VecPivotPos to VecPivotPosLeft
           ; Lookup≢0 to Lookup≢0Left
           ; normTwoRows to normTwoRowsLeft
           )
open module M = AMIF ring hiding (_+ᴹ_)
open module PNormAfter {n} = MatrixPropsAfter (<-strictTotalOrder n) using (_<′_; AllRowsNormalizedRight; simpleFinProps)
module ≈-Reasoning = ReasonSetoid setoid
open module ≋‵ = EqSetoids setoid using (≋-setoid)
open FuncNormAllLines
open FuncNormAndZeros

private variable
  ℓ ℓ′ : Level
  A : Set ℓ
  m n : ℕ

private
  MaybeFin₋ : Fin n ₋ → Set ℓ → Set ℓ
  MaybeFin₋ (just _) = id
  MaybeFin₋ ⊥₋ _ = ⊤

PivValue : Fin m ₋ → Set _
PivValue p = MaybeFin₋ p (Σ[ x ∈ F ] x # 0#)

PivWithValue : ℕ → Set _
PivWithValue m = Σ[ piv ∈ Fin m ₋ ] PivValue piv

findPivAndValue : (xs : Vector F n) → PivWithValue n
findPivAndValue {n = ℕ.zero} xs = ⊥₋ , lift _
findPivAndValue {n = ℕ.suc n} xs with xs (fromℕ _) ≟ 0#
... | yes x#0 = ₋.[ fromℕ _ ] , _ , x#0
... | no _  with findPivAndValue (xs ∘ inject₁)
... | ⊥₋ , _ = ⊥₋ , _
... | ₋.[ p ] , x#0 = ₋.[ inject₁ p ] , x#0

normTwoRows′ : (xs ys : Vector F n) (px py : Fin n ₋) → PivValue px → Vector F n
normTwoRows′ xs ys ⊥₋ py _ = ys
normTwoRows′ xs ys (just px) py (_ , vx#0) = ysn
  where
  open ≈-Reasoning

  vx⁻¹ = #⇒invertible vx#0 .proj₁
  vy = ys px

  -vx⁻¹vy = - (vy * vx⁻¹)
  xsn = -vx⁻¹vy *ₗ xs
  ysn = ys M.+ᴹ xsn

normTwoRows : ∀ (xs ys : Vector F n) (px py : Fin n ₋) (vx : PivValue px) → Vector F n
normTwoRows xs ys ⊥₋ py _ = normTwoRows′ xs ys ⊥₋ py _
normTwoRows xs ys px@(just _) py (_ , vx#0) = normTwoRows′ xs ys px py (_ , vx#0)

normMatrixTwoRowsF′ : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (i j : Fin n) (k : Fin n) (k≟j : Bool) → Vector F m
normMatrixTwoRowsF′ xs pivsXs i j k true
  = normTwoRows (xs i) (xs j) (pivsXs i .proj₁) (pivsXs j .proj₁) (pivsXs i .proj₂)
normMatrixTwoRowsF′ xs pivsXs i j k false = xs k

normMatrixTwoRowsF : ∀ (xs : Matrix F n m) (pivsXs : Vector (PivWithValue m) n)
  (i j : Fin n) → Matrix F n m
normMatrixTwoRowsF xs pivsXs i j k = normMatrixTwoRowsF′ xs pivsXs i j k (does (k F.≟ j))

funcNorm : FuncNormAllLines m n (Matrix F (ℕ.suc n) m)
numberZeros funcNorm xs _ = ⊥₋
normProps funcNorm = simpleFinProps
f (fNormLines funcNorm i j i≢j) xs = normMatrixTwoRowsF xs (findPivAndValue ∘ xs) i j
nZerosProp (fNormLines funcNorm i j i≢j) _ = _

normAfter : Op₁ $ Matrix F n m
normAfter {n = ℕ.zero} xs ()
normAfter {n = ℕ.suc n} = proj₁ ∘ normalizeA funcNorm

normalize : Op₁ $ Matrix F n m
normalize xs = let
  (ys₁ , _) , _ = normalizeMatrix xs
  ys₂ = flip ys₁
  ys₃ = normAfter ys₂
  ys₄ = flip ys₃
  in ys₄


is≠0 : F → Bool
is≠0 x = does $ x ≟ 0#

divideVec : Op₁ $ Vector F n
divideVec {n = n} xs = fromMaybe xs (Maybe.map (λ (_ , inv) i → inv * xs i) (findFirstWithProp xs fMaybe))
  where
  fMaybe : (x : F) → Maybe F
  fMaybe x = Maybe.map (proj₁ ∘ #⇒invertible) (decToMaybe $ x ≟ 0#)

divideByCoeff : Op₁ $ Matrix F n m
divideByCoeff = V.map divideVec

normalizeAndDivide : Op₁ $ Matrix F n m
normalizeAndDivide = divideByCoeff ∘ normalize

func⇒op₁⇒data : Op₁ $ Matrix F n m → Op₁ $ MatrixData F n m
func⇒op₁⇒data f = matrixFunc→Data ∘ f ∘ matrixData→Fun

normalizeData : Op₁ $ MatrixData F n m
normalizeData = func⇒op₁⇒data normalize

normalizeAndDivideData : Op₁ $ MatrixData F n m
normalizeAndDivideData = func⇒op₁⇒data normalizeAndDivide
