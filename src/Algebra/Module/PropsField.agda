open import Algebra
open import Algebra.Apartness
open import Algebra.Module

module Algebra.Module.PropsField
  {c ℓ₁ ℓ₂ mr ℓm}
  (hField : HeytingCommutativeRing c ℓ₁ ℓ₂)
  (leftModule : LeftModule (CommutativeRing.ring
    (HeytingCommutativeRing.commutativeRing hField)) mr ℓm)
  where

open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Product
open import Data.Vec.Functional
open import Relation.Unary.Properties

open import Algebra.Module.Definition leftModule
open import Algebra.BigOps
open import Vector.Structures

open HeytingCommutativeRing hField renaming (Carrier to A)
open CommutativeRing commutativeRing using (rawRing; *-commutativeMonoid)
open LeftModule leftModule renaming (Carrierᴹ to M)
open SumCommMonoid +ᴹ-commutativeMonoid
open VRing rawRing using (_*ⱽ_)
open import Algebra.Solver.CommutativeMonoid *-commutativeMonoid
open import Algebra.HeytingCommutativeRing.Properties hField
open import Algebra.Module.Props commutativeRing leftModule public

import Relation.Binary.Reasoning.Setoid as RSetoid
module ≈ᴹ-Reasoning = RSetoid ≈ᴹ-setoid
module ≈-Reasoning = RSetoid setoid

private variable
  n : ℕ
  xs ys : Vector M n


*#0⊆ⱽ : ∀ (xs : Vector M n) {ys : Vector A n} (ys#0 : ∀ i → ys i # 0#) → xs ⊆ⱽ ys *ᵣ xs
*#0⊆ⱽ {n} xs {ys} ys#0 {x} (zs by xs*zs≈x) = as by ∑as*zs≈x
  where
  ass : _ → _
  ass i = #0⇒invertible (ys#0 i) .proj₁
  as = ass *ⱽ zs

  module _ (i : Fin n) where
    x⁻¹ = #0⇒invertible (ys#0 i) .proj₁
    x⁻¹≈ys = #0⇒invertible (ys#0 i) .proj₂ .proj₁

    as*ys≈zs : as i * ys i ≈ zs i
    as*ys≈zs = begin
      ass i * zs i * ys i ≈⟨ solve 3 (λ a b c → (a ⊕ b) ⊕ c ⊜ (a ⊕ c) ⊕ b) refl (ass i) (zs i) (ys i) ⟩
      x⁻¹   * ys i * zs i ≈⟨ *-congʳ x⁻¹≈ys ⟩
      1# * zs i           ≈⟨ *-identityˡ _ ⟩
      zs i ∎
      where open ≈-Reasoning

    as≈xs : as i *ₗ (ys i *ₗ xs i) ≈ᴹ zs i *ₗ xs i
    as≈xs = begin
        as i *ₗ ys i *ₗ xs i ≈˘⟨ *ₗ-assoc _ _ _ ⟩
        (as i * ys i) *ₗ xs i ≈⟨ *ₗ-congʳ as*ys≈zs ⟩
        zs i *ₗ xs i ∎ where open ≈ᴹ-Reasoning

  ∑as*zs≈x = begin
    ∑ (as *ᵣ (ys *ᵣ xs)) ≈⟨ ∑Ext {n} as≈xs ⟩
    ∑ (zs *ᵣ xs)         ≈⟨ xs*zs≈x ⟩
    x ∎ where open ≈ᴹ-Reasoning

*ₗ#0⊆ⱽ : (xs : Vector M n) (ys : Vector A n) → ys *ᵣ xs ⊆ⱽ xs
*ₗ#0⊆ⱽ {n} xs ys {x} (ws by xs*ws≈x) = as by as*xs≈x
  where
  open ≈ᴹ-Reasoning
  as = ws *ⱽ ys
  as*xs≈x = begin
    ∑ ((ws *ⱽ ys) *ᵣ xs) ≈⟨ ∑Ext {n} (λ _ → *ₗ-assoc _ _ _) ⟩
    ∑ (ws *ᵣ (ys *ᵣ xs)) ≈⟨ xs*ws≈x ⟩
    x ∎

*#0≈ⱽ : ∀ (xs : Vector M n) {ys : Vector A n} (ys#0 : ∀ i → ys i # 0#) → xs ≋ⱽ (ys *ᵣ xs)
*#0≈ⱽ xs ys#0 = record { fwd = *#0⊆ⱽ xs ys#0 ; bwd = *ₗ#0⊆ⱽ xs _ }
