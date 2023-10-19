open import Level using (Level; _⊔_; zero)
open import Data.List
open import Relation.Binary
open import Relation.Binary.Definitions
open import Data.List.Relation.Binary.Pointwise as P using (Pointwise)

module List.ZeroRel {ℓ} {ℓ′} {A : Set ℓ} (_≈_ : Rel A ℓ′) (ε : A) where

private variable
  xs ys : List A
  0# x y x′ y′ : A

infix 4 _≈₀_

private
  _≋_ = Pointwise _≈_

data _≈₀_ : Rel (List A) (ℓ ⊔ ℓ′) where
  refl : xs ≋ ys → xs ≈₀ ys
  prep : x ≈ y → xs ≈₀ ys → x ∷ xs ≈₀ y ∷ ys
  swap : x ≈ x′ → y ≈ y′ → xs ≈₀ ys → x ∷ y ∷ xs ≈₀ y′ ∷ x′ ∷ ys
  trans : Transitive _≈₀_
  add0ₗ : 0# ≈ ε → xs ≈₀ ys → 0# ∷ xs ≈₀ ys
  add0ᵣ : 0# ≈ ε → xs ≈₀ ys → xs ≈₀ 0# ∷ ys

private module Example {refll : Reflexive _≈_} (b c : A) (0# : A) (ε≈0# : ε ≈ 0#) where

  import Data.List.Relation.Binary.Pointwise.Base as P

  theo1 : ε ∷ [ b ] ≈₀ [ b ]
  theo1 = add0ₗ refll (refl (refll P.∷ P.[]))

  _ : b ∷ [ ε ] ≈₀ [ b ]
  _ = trans (swap refll refll (refl P.[])) theo1

  theo3 : [ b ] ≈₀ ε ∷ [ b ]
  theo3 = add0ᵣ refll (refl (refll P.∷ P.[]))

  _ : [ b ] ≈₀ b ∷ [ ε ]
  _ = trans theo3 (swap refll refll (refl P.[]))

  _ : [ ε ] ≈₀ [ 0# ]
  _ = refl (ε≈0# P.∷ P.[])
