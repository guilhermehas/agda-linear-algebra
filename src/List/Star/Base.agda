open import Level using (Level; _⊔_; zero)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric

module List.Star.Base {ℓ} {ℓ′} {A : Set ℓ} (_≈_ : Rel A ℓ′) (0# : A) where

private variable
  xs ys : List A
  0## x y x′ y′ : A

infixr 4 _▹ᴿ_
infix 4 _≈₀_

data _▹ᴿ_ : Rel (List A) (ℓ ⊔ ℓ′) where
  [] : [] ▹ᴿ []
  _∷_ : x ≈ y → xs ▹ᴿ ys → x :: xs ▹ᴿ y :: ys
  swap : x ≈ x′ → y ≈ y′ → xs ▹ᴿ ys → x :: y :: xs ▹ᴿ y′ :: x′ :: ys
  add0ₗ : 0## ≈ 0# → xs ▹ᴿ ys → 0## :: xs ▹ᴿ ys

_≈₀_ = EqClosure _▹ᴿ_

private module Example {refll : Reflexive _≈_} (b c : A) (0## : A) (0#≈0## : 0# ≈ 0##) where

  import Data.List.Relation.Binary.Pointwise.Base as P
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  open StarReasoning (SymClosure _▹ᴿ_)

  _ : 0# :: [ b ] ≈₀ [ b ]
  _ = begin
    0# :: [ b ] ⟶⟨ fwd (add0ₗ refll (refll ∷ [])) ⟩
    [ b ] ∎

  _ : b :: [ 0# ] ≈₀ [ b ]
  _ = begin
    b :: [ 0# ] ⟶⟨ fwd (refll ∷ add0ₗ refll []) ⟩
    [ b ] ∎

  _ : [ b ] ≈₀ 0# :: [ b ]
  _ = begin
    [ b ] ⟶⟨ bwd (add0ₗ refll (refll ∷ [])) ⟩
    0# :: [ b ] ∎

  _ : [ b ] ≈₀ b :: [ 0# ]
  _ = begin
    [ b ] ⟶⟨ bwd (refll ∷ add0ₗ refll []) ⟩
    b :: [ 0# ] ∎

  _ : [ 0# ] ≈₀ [ 0## ]
  _ = begin
    [ 0# ] ⟶⟨ fwd (0#≈0## ∷ []) ⟩
    [ 0## ] ∎
