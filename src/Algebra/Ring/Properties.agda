module Algebra.Ring.Properties where

open import Level
open import Function
open import Algebra
open import Data.Product using (_,_)
open import Relation.Unary

module Units {ℓ ℓ'} (ring : Ring ℓ ℓ') where

  open Ring ring renaming (Carrier to R)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Algebra.Properties.Ring ring public

  0Idempotent : 0# + 0# ≈ 0#
  0Idempotent = +-identityˡ _

  0RightAnnihilates : (x : R) → (x * 0#) ≈ 0#
  0RightAnnihilates x = x+x≈x⇒x≈0 _ (sym x·0-is-idempotent) where
    x·0-is-idempotent : x * 0# ≈ x * 0# + x * 0#
    x·0-is-idempotent = begin
      x * 0#               ≈⟨ *-congˡ (sym 0Idempotent) ⟩
      x * (0# + 0#)        ≈⟨ distribˡ _ _ _ ⟩
      (x * 0#) + (x * 0#)  ∎

  0LeftAnnihilates : (x : R) → (0# * x) ≈ 0#
  0LeftAnnihilates x = x+x≈x⇒x≈0 _ (sym 0·x-is-idempotent) where
    0·x-is-idempotent : 0# * x ≈ 0# * x + 0# * x
    0·x-is-idempotent = begin
      0# * x               ≈⟨ *-congʳ (sym 0Idempotent) ⟩
      (0# + 0#) * x        ≈⟨ distribʳ _ _ _ ⟩
      (0# * x) + (0# * x)  ∎

  invertibleInverse : ∀ {r} → ((r⁻¹ , _) : Invertible _≈_ 1# _*_ (r - 0#)) →
    Invertible _≈_ 1# _*_ (r⁻¹ - 0#)
  invertibleInverse {r} (r⁻¹ , r⁻¹*r≈1 , r*r⁻¹≈1) = r , firstEq , secondEq
    where

      α : ∀ a b → a * - 0# ≈ - 0# * b
      α a b = begin
        a * - 0#  ≈⟨ *-congˡ -0#≈0# ⟩
        a *   0#  ≈⟨ 0RightAnnihilates _ ⟩
        0#       ≈˘⟨ 0LeftAnnihilates  _ ⟩
          0# * b ≈˘⟨ *-congʳ -0#≈0# ⟩
        - 0# * b ∎

      firstEq = begin
        r * (r⁻¹ - 0#)          ≈⟨ distribˡ _ _ _ ⟩
        r * r⁻¹ + r * (- 0#)    ≈⟨ +-congˡ (α _ _) ⟩
        r * r⁻¹ + (- 0#) * r⁻¹ ≈˘⟨ distribʳ _ _ _ ⟩
        (r - 0#) * r⁻¹          ≈⟨ r*r⁻¹≈1 ⟩
        1# ∎

      secondEq = begin
        (r⁻¹ - 0#) * r        ≈⟨ distribʳ _ _ _ ⟩
        r⁻¹ * r + - 0# * r   ≈˘⟨ +-congˡ (α _ _) ⟩
        r⁻¹ * r + r⁻¹ * - 0# ≈˘⟨ distribˡ _ _ _ ⟩
        r⁻¹ * (r - 0#)        ≈⟨ r⁻¹*r≈1 ⟩
        1# ∎
