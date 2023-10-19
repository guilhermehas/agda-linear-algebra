open import Level
open import Function as F
open import Data.Product
open import Relation.Unary
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary.Bundles

module Algebra.VectorSpace.Base {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  where

open Ring ring
open LeftModule leftModule
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
open import Algebra.Solver.CommutativeMonoid +ᴹ-commutativeMonoid
open import Algebra.Definitions (_≐_ {_} {Carrierᴹ} {ℓm})
open import Algebra.SubModule leftModule

private variable
  ℓ ℓ′ : Level
  x y : Carrierᴹ

record isVectorSpace (VS : Cᴹ ℓ) : Set (ℓm ⊔ ℓ) where
  field
    +-closed     : (x∈VS : x ∈ VS) (y∈VS : y ∈ VS) → x +ᴹ y ∈ VS
    0m-closed    : 0ᴹ ∈ VS
    ·-closedLeft : ∀ r (x∈VS : x ∈ VS) → r *ₗ x ∈ VS

open isVectorSpace

0ᴹᴹ = 0ᴹ , 0ᴹ

VectorSpace : (ℓ : Level) → Set (ℓm ⊔ suc ℓ)
VectorSpace ℓ = Σ[ VS ∈ Pred Carrierᴹ ℓ ] isVectorSpace VS

private variable
  s₁ s₂ s₃ : Cᴹ ℓ

0ˢ : isVectorSpace 0ₛ
+-closed 0ˢ {x} {y} x∈VS y∈VS = begin
  x  +ᴹ y  ≈⟨ +ᴹ-cong x∈VS y∈VS ⟩
  0ᴹ +ᴹ 0ᴹ ≈⟨ +ᴹ-identityˡ _ ⟩
  0ᴹ       ∎
0m-closed 0ˢ = ≈ᴹ-refl
·-closedLeft 0ˢ {x} r x∈VS = begin
  r *ₗ x  ≈⟨ *ₗ-congˡ x∈VS ⟩
  r *ₗ 0ᴹ ≈⟨ *ₗ-zeroʳ r ⟩
  0ᴹ ∎

_+ˢ_ : (S1 : isVectorSpace s₁) (S2 : isVectorSpace s₂) → isVectorSpace (s₁ +ₛ s₂)
+-closed (S1 +ˢ S2) {x} {y} ((x₁ , y₁) , x₁∈s , y₁∈s , x+y≈x) ((x₂ , y₂) , x₂∈s , y₂∈s , x+y≈₂x) =
  ((x₁ +ᴹ x₂) , (y₁ +ᴹ y₂)) , +-closed S1 x₁∈s x₂∈s , +-closed S2 y₁∈s y₂∈s ,
  (begin
  (x₁ +ᴹ x₂) +ᴹ (y₁ +ᴹ y₂) ≈⟨ lemma x₁ x₂ y₁ y₂ ⟩
  (x₁ +ᴹ y₁) +ᴹ (x₂ +ᴹ y₂) ≈⟨ +ᴹ-cong x+y≈x x+y≈₂x ⟩
  x +ᴹ y ∎)
  where

  lemma : ∀ x₁ x₂ y₁ y₂ → (x₁ +ᴹ x₂) +ᴹ (y₁ +ᴹ y₂) ≈ᴹ (x₁ +ᴹ y₁) +ᴹ (x₂ +ᴹ y₂)
  lemma = solve 4 (λ x₁ x₂ y₁ y₂ → (x₁ ⊕ x₂) ⊕ (y₁ ⊕ y₂) , (x₁ ⊕ y₁) ⊕ (x₂ ⊕ y₂)) ≈ᴹ-refl

0m-closed (S1 +ˢ S2) = 0ᴹᴹ , 0m-closed S1 , 0m-closed S2 , +ᴹ-identityˡ _
·-closedLeft (S1 +ˢ S2) {z} r ((x , y) , x∈s , y∈s , x+y≈z) = (r *ₗ x , r *ₗ y) ,
  ·-closedLeft S1 r x∈s , ·-closedLeft S2 r y∈s , (begin
  r *ₗ x +ᴹ r *ₗ y ≈˘⟨ *ₗ-distribˡ _ _ _ ⟩
  r *ₗ (x +ᴹ y)    ≈⟨ *ₗ-congˡ x+y≈z ⟩
  r *ₗ z ∎)


spanIsVectorSpace : (v : Carrierᴹ) → isVectorSpace (span v)
+-closed (spanIsVectorSpace v) {a} {b} (x , x∈VS) (y , y∈VS) = x + y , (begin
  (x + y) *ₗ v     ≈⟨ *ₗ-distribʳ _ _ _ ⟩
  x *ₗ v +ᴹ y *ₗ v ≈⟨ +ᴹ-cong x∈VS y∈VS ⟩
  a +ᴹ b ∎)
0m-closed (spanIsVectorSpace v) = 0# , *ₗ-zeroˡ _
·-closedLeft (spanIsVectorSpace v) {x} r (rx , rx∈VS) = (r * rx) , ( begin
  (r * rx) *ₗ v ≈⟨ *ₗ-assoc _ _ _ ⟩
  r *ₗ rx  *ₗ v ≈⟨ *ₗ-congˡ rx∈VS ⟩
  r *ₗ x ∎)
