open import Algebra
open import Algebra.Apartness
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Data.Product

module Algebra.HeytingField.Properties
  {c ℓ₁ ℓ₂} (HF : HeytingField c ℓ₁ ℓ₂) where

open HeytingField HF
open ReasonSetoid setoid

open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing

private variable
  x y z : Carrier

cong-# : x ≈ y → x # z → y # z
cong-# {x} {y} {z} x≈y x#z = invertible⇒# (x-z⁻¹ , theo , theo2) where

  InvXZ : Invertible _≈_ 1# _*_ (x - z)
  InvXZ = #⇒invertible x#z

  x-z⁻¹ = InvXZ .proj₁

  x-z⁻¹*x-z≈1# : x-z⁻¹ * (x - z) ≈ 1#
  x-z⁻¹*x-z≈1# = InvXZ .proj₂ .proj₁

  x-z*x-z⁻¹≈1# : (x - z) * x-z⁻¹ ≈ 1#
  x-z*x-z⁻¹≈1# = InvXZ .proj₂ .proj₂

  theo : x-z⁻¹ * (y - z) ≈ 1#
  theo = begin
    x-z⁻¹ * (y - z) ≈˘⟨ *-congˡ (+-congʳ x≈y) ⟩
    x-z⁻¹ * (x - z)  ≈⟨ x-z⁻¹*x-z≈1# ⟩
    1# ∎

  theo2 : (y - z) * x-z⁻¹ ≈ 1#
  theo2 = trans (*-comm _ _) theo

x⁻¹#0 : (x : Carrier) (x#0 : x # 0#) (let x⁻¹ = #⇒invertible x#0 .proj₁) → x⁻¹ # 0#
x⁻¹#0 x x#0 = invertibleˡ⇒# (x , (begin
  x * (x⁻¹ - 0#) ≈⟨ *-congˡ (x-0≈x _) ⟩
  x * x⁻¹       ≈˘⟨ *-congʳ (x-0≈x _) ⟩
  (x - 0#) * x⁻¹ ≈⟨ #⇒invertible x#0 .proj₂ .proj₂ ⟩
  1# ∎)) where
  x⁻¹ = #⇒invertible x#0 .proj₁
