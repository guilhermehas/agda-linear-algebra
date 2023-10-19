open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Unary.Relation.Binary.Equality
open import Relation.Unary.Properties
open import Algebra
open import Algebra.Module
open import Algebra.Apartness

module Algebra.SubModule.Field {ℓ₁} {ℓ₂} {ℓm}
  (field' : HeytingField ℓm ℓ₁ ℓ₂)
  (let open HeytingField field')
  (let open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing))
  (let open CommutativeRing commutativeRing using (ring; *-commutativeMonoid))
  (leftModule : LeftModule ring ℓm ℓm)
  where

open LeftModule leftModule
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
import Relation.Binary.Reasoning.Setoid setoid as S
open import Algebra.Solver.CommutativeMonoid *-commutativeMonoid
open import Algebra.Properties.Ring ring
open import Algebra.SubModule.Base leftModule
open import Algebra.SubModule.Properties leftModule
import Relation.Binary.Reasoning.Setoid (≐-setoid Carrierᴹ ℓm) as ≐

sameMultipliedˡ : ∀ r (r#0 : r # 0#) v → span v ⊆ span (r *ₗ v)
sameMultipliedˡ r r#0 v {x} (rx , rx*v≈x) = (rx * r⁻¹) , (begin
  (rx * r⁻¹) *ₗ r *ₗ v ≈˘⟨ *ₗ-assoc _ _ _ ⟩
  (rx * r⁻¹ * r) *ₗ v   ≈⟨ *ₗ-congʳ lemma ⟩
  rx *ₗ v               ≈⟨ rx*v≈x ⟩
  x ∎) where

  r⁻¹×Inv = #⇒invertible r#0
  r⁻¹ = r⁻¹×Inv .proj₁

  r⁻¹-0*r≈1 : r * r⁻¹ ≈ 1#
  r⁻¹-0*r≈1 = S.begin
    r * r⁻¹       S.≈˘⟨ *-congʳ (trans (+-congˡ -0#≈0#) (+-identityʳ _)) ⟩
    (r - 0#) * r⁻¹ S.≈⟨ r⁻¹×Inv .proj₂ .proj₂ ⟩
    1# S.∎

  lemma = S.begin
    rx * r⁻¹ * r   S.≈⟨ solve 3 (λ a b c → ((a ⊕ b) ⊕ c) , a ⊕ c ⊕ b) refl rx r⁻¹ r ⟩
    rx * (r * r⁻¹) S.≈⟨ *-congˡ r⁻¹-0*r≈1 ⟩
    rx * 1#        S.≈⟨ *-identityʳ _ ⟩
    rx S.∎

sameMultiplied : ∀ r (r#0 : r # 0#) v → span v ≐ span (r *ₗ v)
sameMultiplied r r#0 v = sameMultipliedˡ r r#0 v , sameMultipliedʳ r v

sameMulitpliedBoth : ∀ r₁ (r₁#0 : r₁ # 0#) r₂ v₁ v₂ →
  (span v₁ +ₛ span v₂) ≐ (span v₁ +ₛ span (r₁ *ₗ v₂ +ᴹ -ᴹ (r₂ *ₗ v₁)))
sameMulitpliedBoth r₁ r₁#0 r₂ v₁ v₂ = ≐.begin
  (span v₁ +ₛ span v₂)          ≐.≈⟨ +ₛ-congˡ (sameMultiplied r₁ r₁#0 v₂) ⟩
  (span v₁ +ₛ span (r₁ *ₗ v₂)) ≐.≈˘⟨ sameAdd (- r₂) _ _ ⟩
  (span v₁ +ₛ span (- r₂ *ₗ v₁ +ᴹ r₁ *ₗ v₂)) ≐.≈⟨ +ₛ-congˡ (cong-span (+ᴹ-comm _ _)) ⟩
  (span v₁ +ₛ span (r₁ *ₗ v₂ +ᴹ - r₂ *ₗ v₁)) ≐.≈⟨ +ₛ-congˡ (cong-span (+ᴹ-congˡ (-→-ᴹ _ _))) ⟩
  (span v₁ +ₛ span (r₁ *ₗ v₂ +ᴹ -ᴹ (r₂ *ₗ v₁))) ≐.∎
