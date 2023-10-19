open import Level
open import Function
open import Data.Product
open import Relation.Unary
open import Algebra.Bundles
open import Algebra.Module
import Algebra.SubModule.Base as SMB

module Algebra.SubModule.SetoidProperties {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  (let open LeftModule leftModule)
  (let open SMB leftModule)
  (≈→∈ : ∀ {x y} {VS : Cᴹ ℓm} → x ≈ᴹ y → x ∈ VS → y ∈ VS)
  where

open Ring ring
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
open import Algebra.SubModule.Properties leftModule public
open import Algebra.Definitions _≅_
open import Algebra.Structures _≅_

L0 = 0ₛ

-- Algebraic properties of _+ₛ_

+ₛ-identityˡ : LeftIdentity 0ₛ _+ₛ_
proj₁ (+ₛ-identityˡ xs) {z} ((0s , x) , 0ss , x∈xs , 0+x≈z) = ≈→∈ x≈z x∈xs
  where
  x≈z = begin
    x       ≈˘⟨ +ᴹ-identityˡ x ⟩
    0ᴹ +ᴹ x ≈˘⟨ +ᴹ-congʳ 0ss ⟩
    0s +ᴹ x  ≈⟨ 0+x≈z ⟩
    z ∎
proj₂ (+ₛ-identityˡ xs) {x} x∈xs = _ , ≈ᴹ-refl , x∈xs , +ᴹ-identityˡ _

+ₛ-identityʳ : RightIdentity 0ₛ _+ₛ_
proj₁ (+ₛ-identityʳ xs) {z} ((x , 0s) , x∈xs , 0ss , x+0≈z) = ≈→∈ x≈z x∈xs
  where
  x≈z = begin
    x       ≈˘⟨ +ᴹ-identityʳ x ⟩
    x +ᴹ 0ᴹ ≈˘⟨ +ᴹ-congˡ 0ss ⟩
    x +ᴹ 0s  ≈⟨ x+0≈z ⟩
    z ∎
proj₂ (+ₛ-identityʳ xs) {x} x∈xs = _ , x∈xs , ≈ᴹ-refl , +ᴹ-identityʳ _

+ₛ-identity : Identity 0ₛ _+ₛ_
+ₛ-identity = +ₛ-identityˡ , +ₛ-identityʳ

-- Structures

+ₛ-0-isMonoid : IsMonoid _+ₛ_ 0ₛ
+ₛ-0-isMonoid = record
  { isSemigroup = +ₛ-isSemigroup
  ; identity = +ₛ-identity
  }

+ₛ-0-isCommutativeMonoid : IsCommutativeMonoid _+ₛ_ 0ₛ
+ₛ-0-isCommutativeMonoid = record
  { isMonoid = +ₛ-0-isMonoid
  ; comm = +ₛ-comm
  }

-- Bundles

+ₛ-0-monoid : Monoid _ _
+ₛ-0-monoid = record
  { isMonoid = +ₛ-0-isMonoid
  }

+ₛ-0-commutativeMonoid : CommutativeMonoid _ _
+ₛ-0-commutativeMonoid = record
  { isCommutativeMonoid = +ₛ-0-isCommutativeMonoid
  }
