open import Algebra.Apartness
open import Relation.Binary

module MatrixFuncNormalization.NormAfter.PropsFlip {c ℓ₁ ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_)
  where

open import Level using (Level; Lift; lift; lower; _⊔_)
open import Function hiding (flip)
open import Data.Product
open import Data.Maybe
open import Data.Nat as ℕ using (ℕ; _∸_; s<s; ≢-nonZero)
open import Data.Nat.Properties as ℕ
  using (≰⇒>; m>n⇒m∸n≢0; pred[m∸n]≡m∸[1+n]; m∸[m∸n]≡n; ∸-monoʳ-<; module ≤-Reasoning)
open import Data.Fin.Base as F hiding (_+_; lift)
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Sum
open import Data.Vec.Functional as V
open import Algebra
import Algebra.Properties.Ring as RingProps
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; refl; cong; subst)
open import Relation.Binary.Construct.Add.Supremum.Strict
open import Relation.Binary.Construct.Add.Infimum.NonStrict
open import Relation.Nullary.Construct.Add.Infimum as ₋
open import Relation.Nullary.Construct.Add.Supremum
import Algebra.Apartness.Properties.HeytingCommutativeRing as HCRProps

open import Algebra.Matrix
import Algebra.HeytingField.Properties as HFProps
import MatrixFuncNormalization.normBef as NormBef
import MatrixFuncNormalization.NormAfter.Base as NormAfterBase
import MatrixFuncNormalization.NormAfter.Properties as NormAfterProperties
open import MatrixFuncNormalization.FinInduction
open import lbry

open hFieldProps hField
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring)
open NormBef hField _≟_ using (normalizeMatrix; AllZeros; _-v_; matrix→matPivs; MatrixWithPivots; matrixPivs)
  renaming ( VecPivotPos to VecPivotPosLeft
           ; Lookup≢0 to Lookup≢0Left
           ; normTwoRows to normTwoRowsLeft
           ; MatrixPivots to MatrixPivotsLeft
           )
open NormAfterBase hField _≟_
open NormAfterProperties hField _≟_ renaming (MatrixWithPivots to MatrixWithPivotsRight)
open PVec
open PNormBef renaming (_<′_ to _<ᴮ_)
open PNormAfter

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ

module FlipProps (xsWithPivs@(xs , pXs , proofPXs) : MatrixWithPivots n m) where

  ys : Matrix F n m
  ys = flip xs

  pYs′ : Vector (VecPivotPosΣ m) n
  proj₁ (pYs′ i) = ys i
  proj₁ (proj₂ (pYs′ i)) with pXs (opposite i)
  ... | ⊥₋ = ⊥₋
  ... | just p = just (opposite p)
  proj₂ (proj₂ (pYs′ i)) with pXs (opposite i) in pXsIEq
  ... | ⊥₋     = _ , help (proofPXs _)
    where
    help : VecPivotPosLeft (xs $ opposite i) (pXs $ opposite i) → AllZeros (ys i)
    help rewrite pXsIEq = λ f → lower f ∘ opposite
  ... | just p = (ys i (opposite p) , help (proofPXs _)) , HF.refl , help2 (proofPXs _)
    where
    help : VecPivotPosLeft (xs $ opposite i) (pXs $ opposite i) → ys i (opposite p) # 0#
    help rewrite pXsIEq | opposite-involutive p  = proj₁

    help2 : VecPivotPosLeft (xs $ opposite i) (pXs $ opposite i) → ∀ j → j F.> opposite p → ys i j ≈ 0#
    help2 rewrite pXsIEq = help3
      where
      open ≤-Reasoning

      sm-sp≡m-p : ℕ.suc (m ∸ ℕ.suc (toℕ p)) ≡ m ∸ toℕ p
      sm-sp≡m-p = begin-equality
        ℕ.suc (m ∸ ℕ.suc (toℕ p)) ≡˘⟨ cong ℕ.suc (pred[m∸n]≡m∸[1+n] m (toℕ p)) ⟩
        ℕ.suc (ℕ.pred (m ∸ toℕ p)) ≡⟨ ℕ.suc-pred (m ∸ toℕ p) ⦃ ≢-nonZero (m>n⇒m∸n≢0 (toℕ<n p)) ⦄ ⟩
        m ∸ toℕ p ∎

      help3 : _
      help3 (_ , p≈0) j opP<j = p≈0 _ opJ<p
        where

        opJ<p : opposite j < p
        opJ<p = begin-strict
          toℕ (opposite j)              ≡⟨ opposite-prop j ⟩
          m ∸ ℕ.suc (toℕ j)             <⟨ ∸-monoʳ-< (s<s opP<j) (toℕ<n j) ⟩
          m ∸ ℕ.suc (toℕ $ opposite p)  ≡⟨ cong (λ x → m ∸ ℕ.suc x) (opposite-prop p) ⟩
          m ∸ ℕ.suc (m ∸ ℕ.suc (toℕ p)) ≡⟨ cong (m ∸_) sm-sp≡m-p ⟩
          m ∸ (m ∸ toℕ p)               ≡⟨ m∸[m∸n]≡n (toℕ≤n p) ⟩
          toℕ p ∎

  pYs : Vector (PivWithValue m) n
  pYs i = let _ , piv , pivValue , _ = pYs′ i in piv , pivValue

  pivsYs : Vector (Fin m ₋) n
  pivsYs = V.map proj₁ pYs

  proofYsPYs : MatrixPivots ys pYs
  proofYsPYs i = let _ , _ , _ , vecPivPos = pYs′ i in vecPivPos

  module NormedRows (allRowsNormed : AllRowsNormalized pXs) where

    private
      <-opposite : ∀ {n} {i j : Fin n} → i < j → opposite j < opposite i
      <-opposite {i = i} {j} i<j  = helper
        where
        helper : toℕ (opposite j) ℕ.< toℕ (opposite i)
        helper rewrite opposite-prop i | opposite-prop j = ∸-monoʳ-< (s<s i<j) (toℕ<n j)


    rowsNormedOpposite : (i j : Fin n) (i<j : i < j) → pXs (opposite j) <ᴮ pXs (opposite i)
    rowsNormedOpposite i j i<j = allRowsNormed (opposite j) (opposite i) (<-opposite i<j)

    allRowsNormedAfter : AllRowsNormalizedRight pivsYs
    allRowsNormedAfter i j i<j = helper (rowsNormedOpposite i j i<j)
      where
      helper : pXs (opposite j) <ᴮ pXs (opposite i) → pivsYs i <′ pivsYs j
      helper with pXs (opposite i) | pXs (opposite j)
      ... | ⊥₋ | ⊥₋  = const $ (⊥₋≤ _)
      ... | ⊥₋ | just _ = const $ (⊥₋≤ _)
      ... | just pi | ⊥₋ = helper2
        where
        helper2 : ⊤⁺ <ᴮ just pi  → _
        helper2 (inj₁ ())
        helper2 (inj₂ ())

      ... | just pi | just pj = helper2
        where
        helper2 : just pj <ᴮ just pi → just (opposite pi) <′ just (opposite pj)
        helper2 (inj₁ [ pj<pi ]) = [ <-opposite pj<pi ]


module _ (xs : Matrix F n m) where

  private
    normedWithProps = normalizeMatrix xs

  ysWithPivots : MatrixWithPivots n m
  ysWithPivots = normedWithProps .proj₁

  ys : Matrix F n m
  ys = ysWithPivots .proj₁

  pYs : Vector (Fin m ⁺) n
  pYs = ysWithPivots .proj₂ .proj₁

  ysPivsProof : MatrixPivotsLeft ys pYs
  ysPivsProof = ysWithPivots .proj₂ .proj₂

  allRowsNormedYsPivs : AllRowsNormalized pYs
  allRowsNormedYsPivs = normedWithProps .proj₂ .proj₁

  xs≈ⱽys : xs ≈ⱽ ys
  xs≈ⱽys = normedWithProps .proj₂ .proj₂

  open FlipProps ysWithPivots using (module NormedRows) renaming (ys to zs; pYs to pvZs; pivsYs to pivsZs)
  open NormedRows allRowsNormedYsPivs

  zs→ws⇒xs≈ⱽws : ∀ {ws} → zs ≈ⱽ ws → xs ≈ⱽ flip ws
  zs→ws⇒xs≈ⱽws zs≈ⱽws = {!!}
