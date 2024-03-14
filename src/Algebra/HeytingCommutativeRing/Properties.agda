open import Algebra.Core
open import Algebra.Apartness
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Data.Product

module Algebra.HeytingCommutativeRing.Properties
  {c ℓ₁ ℓ₂} (HF : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open HeytingCommutativeRing HF
open ReasonSetoid setoid

open import Algebra.Apartness.Properties.HeytingCommutativeRing HF
open import Algebra.Definitions _≈_ using (Invertible)

private variable
  x y z : Carrier

cong-# : x ≈ y → x # z → y # z
cong-# {x} {y} {z} x≈y x#z = invertible⇒# (x-z⁻¹ , theo , theo2) where

  InvXZ : Invertible 1# _*_ (x - z)
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

#0⇒invertible : (x#0 : x # 0#) → Invertible 1# _*_ x
#0⇒invertible {x} x#0 = x⁻¹ , x⁻¹*x≈1 , x*x⁻¹≈1 where
  invX = #⇒invertible x#0
  x⁻¹ = invX .proj₁
  invX1 = invX .proj₂ .proj₁
  invX2 = invX .proj₂ .proj₂

  x⁻¹*x≈1 = begin
    x⁻¹ * x       ≈˘⟨ *-congˡ (x-0≈x _) ⟩
    x⁻¹ * (x - 0#) ≈⟨ invX1 ⟩
    1# ∎
  x*x⁻¹≈1 = begin
    x * x⁻¹       ≈˘⟨ *-congʳ (x-0≈x _) ⟩
    (x - 0#) * x⁻¹ ≈⟨ invX2 ⟩
    1# ∎
