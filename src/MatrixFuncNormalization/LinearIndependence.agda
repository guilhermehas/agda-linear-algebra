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
open import Data.Maybe.Relation.Unary.All
open import Data.Sum
open import Data.Maybe using (is-just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin; fromℕ)
open import Data.Fin.Properties as F
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (refl)

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

module ∑CM {n} = SumCommMonoid (record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid $ leftModule n})
open module DFieldN {n} = DField heytingField (leftModule n)
open module PFieldN {n} = PField heytingField (leftModule n) hiding (module ≈-Reasoning)
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
normLinearDep {ℕ.zero} (xs , pivs , mPivs) _ _ pOne = inj₂ $ λ _ ()
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
  help (ys by xs*ys≈ws) i with pivs i | mPivs i | allR→Monot normed (≤fromℕ i) | cZeros i | pOne i
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
    ... | yes refl = pOneI
    ... | no i≢j = cZ j i≢j

    ysI≈0 = begin
      ys i                          ≈˘⟨ ∑Mul1r ys i ⟩
      ∑ (λ j → δ i j * ys j)         ≈⟨ ∑Ext (λ j → *-comm (δ i j) (ys j)) ⟩
      ∑ (λ j → ys j * δ i j)        ≈˘⟨ ∑Ext {U = λ j → ys j * xs j piv} (*-congˡ ∘ sameXs) ⟩
      ∑ (λ j → ys j * xs j piv)     ≈˘⟨ ∑∑≈∑ {m} {suc n} (λ i j → ys i * xs i j) piv ⟩
      ∑M (λ i j → ys i * xs i j) piv ≈⟨ xs*ys≈ws piv ⟩
      0# ∎

toNormLinearDep : (xs : Matrix F n m) ((ys , pivs , _) : MatrixWithPivots n m)
  → AllRowsNormalized pivs → xs ≋ⱽ ys
  → IsLinearDependent xs ⊎ IsLinearIndependent xs
toNormLinearDep xs (ys , pivs , mPivs) normed xs≋ⱽys = {!!}

decLinearDep : (xs : Matrix F n m) → IsLinearDependent xs ⊎ IsLinearIndependent xs
decLinearDep xs = let mPivs , normed , xs≈ⱽys = normalizeMatrix xs in toNormLinearDep xs mPivs normed $ ≈ⱽ⇒≋ⱽ xs≈ⱽys
