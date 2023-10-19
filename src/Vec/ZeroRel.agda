open import Level using (Level; _⊔_; zero)
open import Data.Nat using (ℕ)
open import Data.Vec
open import Relation.Binary
open import Vec.PermHomogeneous

module Vec.ZeroRel {ℓ} {ℓ′} {A : Set ℓ} (_≈_ : Rel A ℓ′) (ε : A) where

private variable
  m n : ℕ
  xs ys : Vec A n

infix 4 _≈₀_
infix 4 _↭_

private
  _↭_ = Permutation _≈_

data _≈₀_ : Vec A m → Vec A n → Set (ℓ ⊔ ℓ′) where
  permutation : xs ↭ ys → xs ≈₀ ys
  rm0ₗ : ε ∷ xs ≈₀ ys → xs ≈₀ ys
  rm0ᵣ : xs ≈₀ ε ∷ ys → xs ≈₀ ys


private module Example {refll : Reflexive _≈_} (b c : A) (0# : A) (ε≈0# : ε ≈ 0#) where

  import Data.Vec.Relation.Binary.Pointwise.Inductive as P

  _ : ε ∷ [ b ] ≈₀ [ b ]
  _ = rm0ᵣ (permutation (refl (refll P.∷ refll P.∷ P.[])))

  _ : b ∷ [ ε ] ≈₀ [ b ]
  _ = rm0ᵣ (permutation (swap refll refll (refl P.[])))

  _ : [ b ] ≈₀ ε ∷ [ b ]
  _ = rm0ₗ (permutation (refl (refll P.∷ refll P.∷ P.[])))

  _ : [ b ] ≈₀ b ∷ [ ε ]
  _ = rm0ₗ (permutation (swap refll refll (refl P.[])))

  _ : [ ε ] ≈₀ [ 0# ]
  _ = permutation (refl (ε≈0# P.∷ P.[]))
