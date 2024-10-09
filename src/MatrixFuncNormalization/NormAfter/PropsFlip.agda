open import Algebra.Apartness
open import Relation.Binary
open import Algebra.DecidableField

module MatrixFuncNormalization.NormAfter.PropsFlip {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level using (Level; Lift; lift; lower; _⊔_)
open import Function hiding (flip)
open import Data.Product hiding (swap)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All
open import Data.Nat as ℕ using (ℕ; _∸_; s<s; ≢-nonZero)
open import Data.Nat.Properties as ℕ
  using (≰⇒>; m>n⇒m∸n≢0; pred[m∸n]≡m∸[1+n]; m∸[m∸n]≡n; ∸-monoʳ-<; module ≤-Reasoning)
open import Data.Fin.Base as F hiding (_+_; lift)
open import Data.Fin.Properties as F hiding (_≟_)
open import Data.Sum hiding (swap)
open import Data.Vec as Vec using (Vec)
open import Data.Vec.Functional as V
open import Algebra
import Algebra.Properties.Ring as RingProps
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; refl; cong; subst; module ≡-Reasoning)
open import Relation.Binary.Construct.Add.Supremum.Strict
open import Relation.Binary.Construct.Add.Infimum.NonStrict
open import Relation.Nullary.Construct.Add.Infimum as ₋
open import Relation.Nullary.Construct.Add.Supremum
import Algebra.Apartness.Properties.HeytingCommutativeRing as HCRProps
open import Relation.Nullary
import Algebra.Apartness.Properties.HeytingCommutativeRing as HCR
open import Relation.Binary.Construct.Add.Point.Equality

open import Algebra.Matrix
open import Vector.Base using (swapV)
open import Vec.Updates
open import Vec.Relation.FirstOrNot
import Algebra.HeytingField.Properties as HFProps
import MatrixFuncNormalization.normBef as NormBef
import MatrixFuncNormalization.NormAfter.Base as NormAfterBase
import MatrixFuncNormalization.NormAfter.Properties as NormAfterProperties
import MatrixFuncNormalization.MatrixProps as MatrixPropsBefore
open import MatrixFuncNormalization.FinInduction
open import lbry
open import SystemEquations.Definitions dField

open DecidableField dField renaming (Carrier to F; heytingField to hField)
open hFieldProps hField
open HCR heytingCommutativeRing
open NormBef dField using (normalizeMatrix; AllZeros; _-v_; matrix→matPivs; MatrixWithPivots; matrixPivs)
  renaming ( VecPivotPos to VecPivotPosLeft
           ; Lookup≢0 to Lookup≢0Left
           ; normTwoRows to normTwoRowsLeft
           ; MatrixPivots to MatrixPivotsLeft
           ; VecPivotsΣ to VecPivotsLeftΣ
           )
open NormAfterBase dField
open NormAfterProperties dField renaming (MatrixWithPivots to MatrixWithPivotsRight)
open PVec
open module PNorm {n} = MatrixPropsBefore (<-strictTotalOrder n)
  renaming (_<′_ to _<ᴮ_)
open PNormAfter
open MRingProps ring
open import Algebra.Module.Base ring

private variable
  ℓ : Level
  A : Set ℓ
  m n n′ : ℕ

private
  opposite-injective : ∀ {n} {i j : Fin n} → opposite i ≡ opposite j → i ≡ j
  opposite-injective {i = zero} {zero} p = ≡.refl
  opposite-injective {i = zero} {suc j} p = contradiction p fromℕ≢inject₁
  opposite-injective {i = suc i} {zero} p = contradiction (≡.sym p) fromℕ≢inject₁
  opposite-injective {i = suc i} {suc j} p = cong suc (opposite-injective (inject₁-injective p))

  <-opposite : ∀ {n} {i j : Fin n} → i < j → opposite j < opposite i
  <-opposite {i = i} {j} i<j  = helper
    where
    helper : toℕ (opposite j) ℕ.< toℕ (opposite i)
    helper rewrite opposite-prop i | opposite-prop j = ∸-monoʳ-< (s<s i<j) (toℕ<n j)

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
  pivsYs = pivsWV→pivs pYs

  proofYsPYs : MatrixPivots ys pYs
  proofYsPYs i = let _ , _ , _ , vecPivPos = pYs′ i in vecPivPos

  module NormedRows (allRowsNormed : AllRowsNormalized pXs) where
    rowsNormedOpposite : (i j : Fin n) (i<j : i < j) → pXs (opposite j) <ᴮ pXs (opposite i)
    rowsNormedOpposite i j i<j = allRowsNormed (opposite j) (opposite i) (<-opposite i<j)

    allRowsNormedAfter : AllRowsNormalizedRight pivsYs
    allRowsNormedAfter {i} {j} i<j = helper (rowsNormedOpposite i j i<j)
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



module FlipPropsRight (let n = ℕ.suc n′) (xsWithPivs@(xs , pXs , proofPXs) : MatrixWithPivotsRight n m) where

  ys : Matrix F n m
  ys = flip xs

  pYs′ : Vector (VecPivotsLeftΣ m) n
  proj₁ (pYs′ i) = ys i
  proj₁ (proj₂ (pYs′ i)) with pXs (opposite i)
  ... | ⊥₋ , _ = ⊥₋
  ... | just p , p#0 = just (opposite p)
  proj₂ (proj₂ (pYs′ i)) with pXs (opposite i) in PXsIEq
  ... | ⊥₋ , _ = nothing , (lift $ help $ proofPXs _)
    where
    help : VecPivotPos (xs $ opposite i) (pXs (opposite i) .proj₁) (pXs (opposite i) .proj₂) → AllZeros (ys i)
    help rewrite PXsIEq = _∘ opposite
  ... | just j , c , c#0 = just (help3 (proofPXs _)) , help (proofPXs _) , help2 (proofPXs _)
    where
    help : VecPivotPos (xs $ opposite i) (pXs (opposite i) .proj₁) (pXs (opposite i) .proj₂)
      → xs (opposite i) (opposite (opposite j)) # 0#
    help rewrite PXsIEq | opposite-involutive j = λ (c≈res , _) → #-congʳ c≈res c#0

    help2 : VecPivotPos (xs $ opposite i) (pXs (opposite i) .proj₁) (pXs (opposite i) .proj₂)
      → ∀ k → k < opposite j → xs (opposite i) (opposite k) ≈ 0#
    help2 rewrite PXsIEq = help3
      where
      open ≤-Reasoning

      help3 : Lookup≢0 (xs (opposite i)) j c c#0 → ∀ k → k < opposite j → xs (opposite i) (opposite k) ≈ 0#
      help3 (_ , xsI≈0) k k<oj = xsI≈0 _ (begin-strict
        toℕ j                      ≡˘⟨ cong toℕ (opposite-involutive j) ⟩
        toℕ (opposite (opposite j)) <⟨ <-opposite k<oj ⟩
        toℕ (opposite k) ∎)

    help3 : VecPivotPos (xs $ opposite i) (pXs (opposite i) .proj₁) (pXs (opposite i) .proj₂)
      → proj₁ xsWithPivs (opposite i) (opposite (opposite j)) # 0#
    help3 rewrite PXsIEq | opposite-involutive j = λ (c≈res , _) → #-congʳ c≈res c#0

  pYs : Vector (Maybe $ Fin m) n
  pYs i = let _ , piv , _ , _ = pYs′ i in piv

  mYs : MatrixPivotsLeft ys pYs
  mYs i = let _ , _ , _ , d = pYs′ i in d

  module NormedRowsLeft (allRowsNormed : AllRowsNormalizedLeft xs pXs) where

    oppositeRowsNormed : (i j : Fin n) (i≢j : i ≢ j) → Maybe≈0 (xs (opposite j)) (pXs (opposite i) .proj₁)
    oppositeRowsNormed i j i≢j = allRowsNormed (opposite i) (opposite j) (i≢j ∘ opposite-injective)

    columsAreZeroInPivots : AllRowsNormalizedLeft′ ys pYs
    columsAreZeroInPivots i j i≢j = helper (oppositeRowsNormed i j i≢j)
      where
      helper : Maybe≈0 (xs (opposite j)) (pXs (opposite i) .proj₁) → Maybe≈0 (ys j) (pYs i)
      helper with pXs (opposite j) | pXs (opposite i)
      ... | ⊥₋ , _ | ⊥₋ , _ = _
      ... | ⊥₋ , _ | just x , _ rewrite opposite-involutive x = id
      ... | just _ , _ | just x , _ rewrite opposite-involutive x = id
      ... | just _ , _ | ⊥₋ , _ = _


  pXsV = pivsWV→pivs pXs

  module NormedAfter (allRowsNormed : AllRowsNormalizedRight pXsV) where

    allRowsNormedAfter : AllRowsNormalized pYs
    allRowsNormedAfter i j i<j with pXs (opposite j) in eq1 | pXs (opposite i) in eq2 | allRowsNormed (<-opposite i<j)
    ... | just a , _ | just b , _ | [ c ] = inj₁ [ <-opposite c ]
    ... | just a , _ | ⊥₋ , _ | ()
    ... | ⊥₋ , _ | just b , _ | ⊥₋≤ _ = inj₁ [ _ ]<⊤⁺
    ... | ⊥₋ , _ | ⊥₋ , _ | c  = inj₂ (∙≈∙ , ∙≈∙)



module PropsMatrix (let n = ℕ.suc n′) (xs : Matrix F n m) where

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

  open FlipProps ysWithPivots using (module NormedRows; proofYsPYs) renaming (ys to zs; pYs to pvZs; pivsYs to pivsZs)
  open NormedRows allRowsNormedYsPivs

  mOpsInv≡ : ∀ mOps (zs : Matrix F n m) i j → matOps→func (opVecOps {n} mOps) (flip zs) i j ≡
    matOps→func mOps zs (opposite i) (opposite j)
  mOpsInv≡ (swapOp p q p≢q) zs i j = begin
    swapV fzs (opposite p) (opposite q) i j ≡⟨ cong (λ xs → xs j)
      (vecUpdates≡reflectBool-theo2 fzs indices values i) ⟩
    evalFromPosition values (fzs i) evaluated j
      ≡⟨ helper _ _ (vBoolFromIndices indices i .proj₂) (vBoolFromIndices indices₂ (opposite i) .proj₂) ⟩
    evalFromPosition values₂ (zs (opposite i)) evaluated₂ (opposite j) ≡˘⟨ cong (λ xs → xs (opposite j))
      (vecUpdates≡reflectBool-theo2 zs indices₂ values₂ (opposite i)) ⟩
    swapV zs p q (opposite i) (opposite j) ∎
    where
    open ≡-Reasoning

    fzs = flip zs

    indices = opposite q Vec.∷ opposite p Vec.∷ Vec.[]
    values = fzs (opposite p) Vec.∷ fzs (opposite q) Vec.∷ Vec.[]
    evaluated = firstTrue $ proj₁ $ vBoolFromIndices indices i

    indices₂ = q Vec.∷ p Vec.∷ Vec.[]
    values₂ = zs p Vec.∷ zs q Vec.∷ Vec.[]
    evaluated₂ = firstTrue $ proj₁ $ vBoolFromIndices indices₂ (opposite i)

    helper : ∀ vBool₁ vBool₂
      → VecWithType (λ (ind , b) → Reflects (i ≡ ind) b) $ Vec.zip indices vBool₁
      → VecWithType (λ (ind , b) → Reflects (opposite i ≡ ind) b) $ Vec.zip indices₂ vBool₂
      → evalFromPosition values (fzs i) (firstTrue vBool₁) j ≡
        evalFromPosition values₂ (zs (opposite i)) (firstTrue vBool₂) (opposite j)
    helper (true Vec.∷ vBool₁) (true Vec.∷ vBool₂) (ofʸ ≡.refl ∷ p) (ofʸ _ ∷ q) =
      cong (λ i → zs i (opposite j)) (opposite-involutive _)
    helper (true Vec.∷ vBool₁) (false Vec.∷ vBool₂) (ofʸ ≡.refl ∷ p) (ofⁿ ¬a ∷ q) =
      contradiction (opposite-involutive _) ¬a
    helper (false Vec.∷ vBool₁) (true Vec.∷ vBool₂) (ofⁿ ¬a ∷ p) (ofʸ ≡.refl ∷ q) =
      contradiction (≡.sym (opposite-involutive _)) ¬a
    helper (false Vec.∷ false Vec.∷ Vec.[]) (false Vec.∷ true Vec.∷ Vec.[])
      (ofⁿ ¬a ∷ ofⁿ ¬c ∷ []) (ofⁿ ¬b ∷ ofʸ ≡.refl ∷ []) =
      contradiction (≡.sym (opposite-involutive _)) ¬c
    helper (false Vec.∷ true Vec.∷ Vec.[]) (false Vec.∷ false Vec.∷ Vec.[]) (ofⁿ ¬a ∷ ofʸ ≡.refl ∷ []) (ofⁿ ¬b ∷ ofⁿ ¬c ∷ []) =
      contradiction (opposite-involutive _) ¬c
    helper (false Vec.∷ true Vec.∷ Vec.[]) (false Vec.∷ true Vec.∷ Vec.[]) (ofⁿ ¬a ∷ ofʸ ≡.refl ∷ []) (ofⁿ ¬b ∷ ofʸ _ ∷ [])
      = cong (λ x → zs x (opposite j)) (opposite-involutive _)
    helper (false Vec.∷ false Vec.∷ Vec.[]) (false Vec.∷ false Vec.∷ Vec.[]) (ofⁿ ¬a ∷ ofⁿ ¬c ∷ []) (ofⁿ ¬b ∷ ofⁿ ¬a₁ ∷ []) = ≡.refl

  mOpsInv≡ (addCons p q p≢q r) zs i j with opposite q F.≟ i | q F.≟ opposite i
  ... | yes ≡.refl | yes _ = cong (λ x → _ + _ * zs x _) (opposite-involutive _)
  ... | yes ≡.refl | no ¬p = contradiction (≡.sym (opposite-involutive _)) ¬p
  ... | no ¬p | yes ≡.refl = contradiction (opposite-involutive _) ¬p
  ... | no _ | no _ = ≡.refl

  open ≈-Reasoning

  zs≈ⱽws⇒ys≈ⱽws : ∀ {ws} → zs ≈ⱽ ws → ys ≈ⱽ flip ws
  zs≈ⱽws⇒ys≈ⱽws {ws} (idR zs≈ws) = idR $ λ i j → begin
    ys i j            ≈˘⟨ flip-flip ys _ _ ⟩
    flip (flip ys) i j ≈⟨ zs≈ws _ _ ⟩
    flip ws i j ∎
  zs≈ⱽws⇒ys≈ⱽws {ws} (rec {ys = zs} mOps zs≈ⱽws mOps≈) = rec (opVecOps mOps) (zs≈ⱽws⇒ys≈ⱽws zs≈ⱽws)
    λ i j → begin
      matOps→func (opVecOps mOps) (flip zs) i j     ≡⟨ mOpsInv≡ mOps zs i j ⟩
      matOps→func mOps zs (opposite i) (opposite j) ≈⟨ mOps≈ (opposite i) (opposite j) ⟩
      flip ws i j ∎

  zs≈ⱽws⇒xs≈ⱽws : ∀ {ws} → zs ≈ⱽ ws → xs ≈ⱽ flip ws
  zs≈ⱽws⇒xs≈ⱽws = ≈ⱽ-trans xs≈ⱽys ∘ zs≈ⱽws⇒ys≈ⱽws

  wsWithProps : Σ[ (ws , xs≈ⱽws , _) ∈ _ ] _
  wsWithProps = normMatrix _ _ proofYsPYs allRowsNormedAfter (zs , ≈ⱽ-refl , proofYsPYs)

  ws = wsWithProps .proj₁ .proj₁
  wsPivs = wsWithProps .proj₁ .proj₂ .proj₁
  wsProp = wsWithProps .proj₂

  wsPivots : MatrixPivots ws pvZs
  wsPivots = wsWithProps .proj₁ .proj₂ .proj₂

  wsNormedLeft : AllRowsNormalizedLeft ws pvZs
  wsNormedLeft = allNormedLeft _ _ (wsWithProps .proj₁ .proj₂ .proj₂) allRowsNormedAfter wsProp

  open FlipPropsRight (ws , pvZs , wsPivots) renaming (ys to nxs; pYs to pZs)
    using (module NormedRowsLeft; module NormedAfter; mYs) public
  open NormedRowsLeft wsNormedLeft public
  open NormedAfter allRowsNormedAfter public

  xs≈ⱽnxs : xs ≈ⱽ nxs
  xs≈ⱽnxs = zs≈ⱽws⇒xs≈ⱽws $ wsWithProps .proj₁ .proj₂ .proj₁

allTheoremsTogether : (xs : Matrix F n m) →
  -- transformed matrix
  Σ[ ys ∈ Matrix F n m ]

  -- positions of the pivots in ys
  Σ[ pivs ∈ Vector (Fin m ⁺) n ]

  -- ys is 0 to the left of the pivots positions and non zero in the pivot position
  MatrixPivotsLeft ys pivs

  -- A list of transformation steps from xs to ys and
  -- a proof xs span to the same vector space of ys
  -- TODO: more explanation, added matrix
  × xs ≈ⱽ ys

  -- Everything above each pivot is zero and
  -- everything below each pivot is zero
  × ColumnsZero ys  pivs

  -- The pivots are an increase list
  -- TODO: It should be earlier
  × AllRowsNormalized pivs
allTheoremsTogether {ℕ.zero} xs = (λ ()) , (λ ()) , (λ ()) , idR (λ ()) , (λ ()) , λ ()
allTheoremsTogether {ℕ.suc n} xs = _ , _ , mYs , xs≈ⱽnxs , columsAreZeroInPivots , allRowsNormedAfter
  where open PropsMatrix xs
