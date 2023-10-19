open import Level renaming (zero to lzero)
open import Algebra.Bundles
open import Algebra.Module
open import Data.List
open import Data.List.Relation.Binary.Permutation.Homogeneous

module Algebra.SubModule.Relation.Base {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

  infix 4 _≈ᴿ_

  open Ring ring
  open LeftModule leftModule
  open import List.ZeroRel _≈ᴹ_ 0ᴹ

  private variable
    r s : Carrier
    x x′ y y′ : Carrierᴹ
    xs xs′ ys ys′ : List Carrierᴹ

  data _≈ᴿ_ : List Carrierᴹ → List Carrierᴹ → Set (ℓm ⊔ ℓm′ ⊔ ℓr) where
    sameZeros : xs ≈₀ ys → xs ≈ᴿ ys
    sameZerosBothSides : xs ≈₀ xs′ → ys ≈₀ ys′ → xs ≈ᴿ ys → xs′ ≈ᴿ ys′
    addedVec : x ∷ y ∷ xs ≈ᴿ x′ ∷ y′ ∷ ys
      → x +ᴹ r *ₗ y ∷ y ∷ xs ≈ᴿ x′ +ᴹ s *ₗ y′ ∷ y′ ∷ ys
