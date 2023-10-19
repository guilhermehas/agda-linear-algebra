module Algebra.CommRing.Properties where

open import Level
open import Function
open import Algebra
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Unary
import Algebra.Ring.Properties as RP

private
  variable
    ℓ ℓ' ℓ'' : Level

module Units (R' : CommutativeRing ℓ ℓ') where

  open CommutativeRing R' renaming (Carrier to R)
  open import Relation.Binary.Reasoning.Setoid setoid
  open RP.Units ring

  semiRing : RawSemiring _ _
  semiRing = record { Carrier = R ; _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; 0# = 0# ; 1# = 1# }
  open import Algebra.Definitions.RawSemiring semiRing

  Rˣ : Pred R _
  Rˣ r = Σ[ r' ∈ R ] ((r * r') ≈ 1#)

  RˣContainsOne : 1# ∈ Rˣ
  RˣContainsOne = 1# , *-identity .proj₁ 1#

  *-rinv : (r : R) (r∈Rˣ : r ∈ Rˣ) → r * r∈Rˣ .proj₁ ≈ 1#
  *-rinv r r∈Rˣ = r∈Rˣ .proj₂

  RˣMultClosed : (r r' : R) (r∈Rˣ : r ∈ Rˣ) (r'∈Rˣ : r' ∈ Rˣ)
                → (r * r') ∈ Rˣ
  RˣMultClosed r r' r∈Rˣ r'∈Rˣ = r⁻¹ * r'⁻¹ , path where
    r⁻¹  = r∈Rˣ .proj₁
    r'⁻¹ = r'∈Rˣ .proj₁

    path : r * r' * (r⁻¹ * r'⁻¹) ≈ 1#
    path = begin
      r * r' * (r⁻¹ * r'⁻¹) ≈⟨ *-congʳ (*-comm _ _) ⟩
      r' * r * (r⁻¹ * r'⁻¹) ≈⟨ (sym $ *-assoc _ _ _) ⟩
      r' * r * r⁻¹ * r'⁻¹   ≈⟨ *-congʳ (*-assoc _ _ _) ⟩
      r' * (r * r⁻¹) * r'⁻¹ ≈⟨ *-congʳ (*-congˡ (*-rinv r r∈Rˣ)) ⟩
      r' * 1# * r'⁻¹        ≈⟨ *-congʳ (*-identityʳ _) ⟩
      r' * r'⁻¹             ≈⟨ *-rinv r' r'∈Rˣ ⟩
      1# ∎

  ^-presUnit : ∀ (f : R) (n : ℕ) → f ∈ Rˣ → f ^ n ∈ Rˣ
  ^-presUnit f zero f∈Rˣ = RˣContainsOne
  ^-presUnit f (suc n) f∈Rˣ = RˣMultClosed f (f ^ n) f∈Rˣ (^-presUnit f n f∈Rˣ)

  UnitsAreNotZeroDivisors : (r : R) (r∈Rˣ : r ∈ Rˣ)
    → ∀ r' → r' * r ≈ 0# → r' ≈ 0#
  UnitsAreNotZeroDivisors r r∈Rˣ r' p = let r⁻¹ = r∈Rˣ .proj₁ in begin
    r'             ≈˘⟨ *-identityʳ _ ⟩
    r' * 1#        ≈⟨ *-congˡ (sym (*-rinv _ r∈Rˣ)) ⟩
    r' * (r * r⁻¹) ≈˘⟨ *-assoc _ _ _ ⟩
    r' * r * r⁻¹   ≈⟨ *-congʳ p ⟩
    0# * r⁻¹       ≈⟨ 0LeftAnnihilates _ ⟩
    0# ∎
