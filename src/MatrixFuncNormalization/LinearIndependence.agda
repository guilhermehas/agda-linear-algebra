open import Algebra.DecidableField

module MatrixFuncNormalization.LinearIndependence {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Level hiding (suc)
open import Algebra
open import Algebra.Apartness
open import Algebra.Module.Bundles
open import Algebra.Matrix
open import Function using (_$_; _∘_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Maybe
open import Data.Sum
open import Data.Maybe using (is-just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin; fromℕ)
open import Data.Fin.Properties as F
open import Relation.Nullary

open import Algebra.BigOps
import MatrixFuncNormalization.normBef as NormBef
import Algebra.Module.DefsField as DField
import Algebra.Module.PropsField as PField

open DecidableField dField renaming (Carrier to F) hiding (sym)
open NormBef dField
open import MatrixFuncNormalization.NormAfter.Properties dField using (ColumnsZero)
open HeytingField heytingField using (heytingCommutativeRing)
open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (ring; sym)
open import Algebra.Module.Instances.FunctionalVector ring
open PNorm
open PVec hiding (module ≈ᴹ-Reasoning)
open SumRing ring using (δ; δii≡1#)
open LeftModule using (+ᴹ-isCommutativeMonoid)

open module ∑CM {n} = SumCommMonoid (record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid (leftModule n)})
open module DFieldN {n} = DField heytingField (leftModule n)
open module PFieldN {n} = PField heytingField (leftModule n) hiding (module ≈-Reasoning)

private variable
  m n : ℕ

-- isLinearIndependentNormed : Matrix F n m → Bool
-- isLinearIndependentNormed {zero}  xs = true
-- isLinearIndependentNormed {suc n} xs = is-just $ proj₁ $ findPivAndValue $ xs $ fromℕ _

-- isLinearDependentNormed : Matrix F n m → Bool
-- isLinearDependentNormed = not ∘ isLinearIndependentNormed

-- isLinearIndependent : Matrix F n m → Bool
-- isLinearIndependent = isLinearIndependentNormed ∘ normalize

-- isLinearDependent : Matrix F n m → Bool
-- isLinearDependent = not ∘ isLinearIndependent

open _reaches_
open ≈ᴹ-Reasoning

normLinearDep : ((xs , pivs , _) : MatrixWithPivots n m)
  → AllRowsNormalized pivs
  → ColumnsZero xs pivs
  → IsLinearDependent xs ⊎ IsLinearIndependent xs
normLinearDep {ℕ.zero} (xs , pivs , mPivs) _ _ = inj₂ $ λ _ ()
normLinearDep {suc n} {m} (xs , pivs , mPivs) normed cZeros with pivs $ fromℕ _ in pivEq | mPivs $ fromℕ _
... | nothing | lift allZ = inj₁ help
  where
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
  help (ys by xs*ys≈ws) i with pivs i | mPivs i | normed i (fromℕ n) {!toℕ<n!}
  ... | nothing | lift allZ | inj₂ (_ , q) rewrite pivEq = help2 q
    where
    help2 : _ → _
    help2 ()
  ... | just piv | xsIP#0 , xsIJ≈0 | inj₁ <-ineq = {!!}


toNormLinearDep : (xs : Matrix F n m) ((ys , pivs , _) : MatrixWithPivots n m) → AllRowsNormalized pivs → xs ≋ⱽ ys
  → IsLinearDependent xs ⊎ IsLinearIndependent xs
toNormLinearDep xs (ys , pivs , mPivs) normed xs≋ⱽys = {!!}

decLinearDep : (xs : Matrix F n m) → IsLinearDependent xs ⊎ IsLinearIndependent xs
decLinearDep xs = let mPivs , normed , xs≈ⱽys = normalizeMatrix xs in toNormLinearDep xs mPivs normed (≈ⱽ⇒≋ⱽ xs≈ⱽys)
