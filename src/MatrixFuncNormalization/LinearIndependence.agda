open import Algebra.DecidableField

module MatrixFuncNormalization.LinearIndependence {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level hiding (suc)
open import Algebra
open import Algebra.Apartness
open import Algebra.Module.Bundles
open import Algebra.Matrix
open import Function using (_$_; _∘_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂; _,_; ∃)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All
open import Data.Sum
open import Data.Maybe using (is-just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin; fromℕ)
open import Data.Fin.Properties as F
open import Data.Vec.Functional as V
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Algebra.BigOps
import MatrixFuncNormalization.normBef as NormBef
import Algebra.Module.DefsField as DField
import Algebra.Module.PropsField as PField

open import MatrixFuncNormalization.MainTheo dField
open DecidableField dField renaming (Carrier to F)
open NormBef dField
open import MatrixFuncNormalization.NormAfter.Properties dField using (ColumnsZero)
open import MatrixFuncNormalization.ElimZeros.Properties dField hiding
  (module PFieldN)
open import Algebra.HeytingCommutativeRing.Properties heytingCommutativeRing
open import Algebra.Module.Instances.FunctionalVector ring
open PNorm
open SumRing ring using (δ; δii≡1#)
open LeftModule using (+ᴹ-isCommutativeMonoid)

import Algebra.Solver.CommutativeMonoid *-commutativeMonoid as *-Solver hiding (_≟_)
module ∑CM {n} = SumCommMonoid (record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid $ leftModule n})
open module DFieldN {n} = DField heytingField (leftModule n)
open module PFieldN {n} = PField dField (leftModule n) hiding (module ≈-Reasoning)
open import Algebra.Module.PropsVec commutativeRing using (∑∑≈∑)
open import MatrixFuncNormalization.Definitions dField

private variable
  m n : ℕ

open _reaches_

normLinearDep : ((xs , pivs , _) : MatrixWithPivots n m)
  → AllRowsNormalized pivs
  → ColumnsZero xs pivs
  → PivsOne≁0⁺ xs pivs
  → IsLinearDependent xs ⊎ IsLinearIndependent xs
normLinearDep {ℕ.zero} (xs , pivs , mPivs) _ _ pOne = inj₂ λ _ ()
normLinearDep {suc n} {m} (xs , pivs , mPivs) normed cZeros pOne with pivs $ fromℕ _ in pivEq | mPivs $ fromℕ _
... | nothing | lift allZ = inj₁ help
  where
  open ≈ᴹ-Reasoning
  open ∑CM

  help : IsLinearDependent xs
  ys (proj₁ help) = δ $ fromℕ _
  xs*ys≈x (proj₁ help) = begin
    ∑ {m} (λ i → δ (fromℕ n) i *ₗ xs i) ≈⟨ δ*ᵣ-refl xs _ ⟩
    xs (fromℕ n) ≈⟨ allZ ⟩
    0ᴹ ∎
  proj₁ (proj₂ help) = fromℕ _
  proj₂ (proj₂ help)  = #-congʳ (sym $ reflexive $ δii≡1# $ fromℕ n) 1#0

... | just j | xsN#0 , _ = inj₂ help
  where
  help : IsLinearIndependent xs
  help {ys} xs*ys≈ws i with pivs i | mPivs i | allR→Monot normed (≤fromℕ i) | cZeros i | pOne i
  ... | nothing | lift allZ | inj₁ () | _ | _
  ... | nothing | lift allZ | inj₂ q  | _ | _ rewrite pivEq = help2 q
    where
    help2 : _ → _
    help2 ()
  ... | just piv | xsIP#0 , xsIJ≈0 | _ | cZ | just pOneI = ysI≈0

    where
    open ≈-Reasoning
    open ∑CM renaming (∑ to ∑M) using ()
    open SumRing ring using (∑; ∑Ext; ∑Mul1r)

    sameXs : ∀ j → xs j piv ≈ δ i j
    sameXs j with i F.≟ j
    ... | yes ≡.refl = pOneI
    ... | no i≢j = cZ j i≢j

    ysI≈0 =  begin
      ys i                          ≈˘⟨ ∑Mul1r ys i ⟩
      ∑ (λ j → δ i j * ys j)         ≈⟨ ∑Ext (λ j → *-comm (δ i j) (ys j)) ⟩
      ∑ (λ j → ys j * δ i j)        ≈˘⟨ ∑Ext {U = λ j → ys j * xs j piv} (*-congˡ ∘ sameXs) ⟩
      ∑ (λ j → ys j * xs j piv)     ≈˘⟨ ∑∑≈∑ {m} {suc n} (λ i j → ys i * xs i j) piv ⟩
      ∑M (λ i j → ys i * xs i j) piv ≈⟨ xs*ys≈ws piv ⟩
      0# ∎


divZeroSameLinRev : (xsNorm : MatrixNormed n m) (open MatrixNormed xsNorm) (open MatNormed xsNorm renaming (ys to zs)) → ∀ b
  → LinearIndependent? xs b
  → LinearIndependent? zs b
divZeroSameLinRev {n = n} {m} xsNorm _ (linDep (ys by xs*ys≈x , i , ysI#0)) = linDep (ws by ∑Same , i , wsI#0)
  where
  open MatrixNormed xsNorm
  open MatNormed xsNorm renaming (ys to zs)
  open ∑CM
  open *-Solver

  ws : Vector _ _
  ws j = multiplyF (xs j) (pivs j) * ys j

  ws*zs≈ys*xs : ∀ i j → ws i * zs i j ≈ ys i * xs i j
  ws*zs≈ys*xs i j = begin
    multiplyF (xs i) (pivs i) * ys i  * zs i j  ≈⟨ solve 3 (λ a b c → ((a ⊕ b) ⊕ c) , (b ⊕ a ⊕ c)) refl _ _ _ ⟩
    ys i * (multiplyF (xs i) (pivs i) * zs i j) ≈⟨ *-congˡ (multiply*divide≈same (xs i) (pivs i) _ j) ⟩
    ys i * xs i j ∎ where open ≈-Reasoning

  ∑Same = begin
    ∑ (ws *ᵣ zs) ≈⟨ ∑Ext {n} {m} ws*zs≈ys*xs ⟩
    ∑ (ys *ᵣ xs) ≈⟨ xs*ys≈x ⟩
    0ᴹ ∎ where open ≈ᴹ-Reasoning

  wsI#0 : ws i # 0#
  wsI#0 = x#0y#0→xy#0 (multiplyF#0 (xs i) (pivs i) (mPivots i)) ysI#0


divZeroSameLinRev xsNorm _ (linInd lInd) = linInd  help
  where
  open MatrixNormed xsNorm
  open MatNormed xsNorm renaming (ys to zs)
  open ∑CM
  open *-Solver

  help : ∀ {ws} (_ : _ reaches 0ᴹ by ws) i → ws i ≈ 0#
  help {ws} ws*zs≈0 i = x#0*y≈0⇒y≈0 (divideF#0 (xs i) (pivs i) _) (ldKs i)
    where
    rs : Vector _ _
    rs j = divideF (xs j) (pivs j) (mPivots j)

    ks : Vector _ _
    ks j = rs j * ws j

    ks*xs≈ws*zs : ∀ i j → ks i * xs i j ≈ ws i * zs i j
    ks*xs≈ws*zs i j = begin
      rs i * ws i * xs i j   ≈⟨ solve 3 (λ a b c → ((a ⊕ b) ⊕ c) , (b ⊕ a ⊕ c)) refl _ _ _ ⟩
      ws i * (rs i * xs i j) ≈⟨ *-congˡ (divideF*vec≈divideVec (xs i) (pivs i) _ _) ⟩
      ws i * zs i j ∎ where open ≈-Reasoning

    ∑ks*xs≈0 = begin
      ∑ (ks *ᵣ xs) ≈⟨ ∑Ext ks*xs≈ws*zs ⟩
      ∑ (ws *ᵣ zs) ≈⟨ ws*zs≈0 ⟩
      0ᴹ ∎ where open ≈ᴹ-Reasoning

    ldKs : is0 ks
    ldKs =  lInd ∑ks*xs≈0

divZeroSameLin : (xsNorm : MatrixNormed n m) (open MatrixNormed xsNorm) (open MatNormed xsNorm renaming (ys to zs)) → ∀ b
  → LinearIndependent? zs b
  → LinearIndependent? xs b
divZeroSameLin {n = n} {m} xsNorm _ (linDep (ys by xs*ys≈x , i , ysI#0)) = linDep (ws by ∑Same , i , wsI#0)
  where
  open MatrixNormed xsNorm
  open MatNormed xsNorm renaming (ys to zs)
  open ∑CM
  open *-Solver

  ks : Vector _ _
  ks j = divideF (xs j) (pivs j) (mPivots j)

  ws : Vector _ _
  ws j = ks j * ys j

  ws*xs≈ys*zs = λ i j → begin
    ws i * xs i j       ≈⟨ solve 3 (λ a b c → ((a ⊕ b) ⊕ c) , (b ⊕ a ⊕ c)) refl _ _ _ ⟩
    ys i * (_ * xs i j) ≈⟨ *-congˡ (divideF*vec≈divideVec (xs i) (pivs i) _ _) ⟩
    ys i * zs i j ∎
    where open ≈-Reasoning

  ∑Same = begin
    ∑ (ws *ᵣ xs) ≈⟨ ∑Ext {n} {m} ws*xs≈ys*zs ⟩
    ∑ (ys *ᵣ zs) ≈⟨ xs*ys≈x ⟩
    0ᴹ ∎
    where open ≈ᴹ-Reasoning

  wsI#0 = x#0y#0→xy#0 (divideF#0 (xs i) (pivs i) _) ysI#0

divZeroSameLin xsNorm _ (linInd lInd) = linInd help
  where
  open MatrixNormed xsNorm
  open MatNormed xsNorm renaming (ys to zs)
  open ∑CM
  open *-Solver

  help : ∀ {ws} (_ : xs reaches 0ᴹ by ws) i → ws i ≈ 0#
  help {ws} ws*zs≈0 i = x#0*y≈0⇒y≈0 (multiplyF#0 (xs i) (pivs i) (mPivots i)) (ldKs i)
    where
    rs : Vector _ _
    rs j = multiplyF (xs j) (pivs j)

    ks : Vector _ _
    ks j = rs j * ws j

    ks*xs≈ws*zs : ∀ i j → ks i * zs i j ≈ ws i * xs i j
    ks*xs≈ws*zs i j = begin
      rs i * ws i * zs i j   ≈⟨ solve 3 (λ a b c → ((a ⊕ b) ⊕ c) , (b ⊕ a ⊕ c)) refl _ _ _ ⟩
      ws i * (rs i * zs i j) ≈⟨ *-congˡ (multiply*divide≈same (xs i) (pivs i) _ _) ⟩
      ws i * xs i j ∎ where open ≈-Reasoning

    ∑ks*xs≈0 = begin
      ∑ (ks *ᵣ zs) ≈⟨ ∑Ext ks*xs≈ws*zs ⟩
      ∑ (ws *ᵣ xs) ≈⟨ ws*zs≈0 ⟩
      0ᴹ ∎ where open ≈ᴹ-Reasoning

    ldKs : is0 ks
    ldKs = lInd ∑ks*xs≈0

decLinearDep : (xs : Matrix F n m) → ∃ $ LinearIndependent? xs
decLinearDep xs = _ , sameLd (sameLd3 (proj₂ (help linDepYs)))
  where
  open FromNormalization (normalize xs) renaming (ys to ws; ysNormed to wsNormed)
  open MatNormed (record { isNormed = wsNormed }) renaming (ys to zs)

  linDepYs : IsLinearDependent zs ⊎ IsLinearIndependent zs
  linDepYs = normLinearDep (zs , pivs , mPivAfter) pivsCrescent columnsZeros pivsOne

  sameLd : ∀ {b} → LinearIndependent? ws b → LinearIndependent? xs b
  sameLd = sameLin ws xs (≈ⱽ-sym xs≈ⱽys) _

  sameLd2 : ∀ {b} → LinearIndependent? ws b → LinearIndependent? zs b
  sameLd2 = divZeroSameLinRev (record { isNormed = wsNormed }) _

  sameLd3 : ∀ {b} → LinearIndependent? zs b → LinearIndependent? ws b
  sameLd3 = divZeroSameLin (record { isNormed = wsNormed }) _

  help : IsLinearDependent zs ⊎ IsLinearIndependent zs → ∃ (LinearIndependent? zs)
  help (inj₁ lDep) = _ , linDep lDep
  help (inj₂ lInd) = _ , linInd lInd
