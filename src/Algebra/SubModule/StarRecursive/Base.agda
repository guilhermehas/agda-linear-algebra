open import Level using (Level; _⊔_; zero)
open import Algebra.SubModule.Base
open import Algebra
open import Algebra.Module
open import Data.List renaming (_∷_ to _::_)
open import Data.List.Relation.Binary.Pointwise.Base
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric as S
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

module Algebra.SubModule.StarRecursive.Base {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

open Ring ring
open LeftModule leftModule renaming (Carrierᴹ to A)

private variable
  xs ys : List A
  r : Carrier
  x0 x y x′ y′ : A

infixr 4 _▹ᴿ_ _≈ᴿ_ _∽_
infixr 5 _∷_

data _▹ᴿ_ : Rel (List A) (ℓm ⊔ ℓm′ ⊔ ℓr) where
  []        : [] ▹ᴿ []
  _∷_       : x ≈ᴹ y   → xs ▹ᴿ ys → x :: xs ▹ᴿ y :: ys
  swap      : x ≈ᴹ x′  → y ≈ᴹ y′  → xs ▹ᴿ ys → x :: y :: xs ▹ᴿ y′ :: x′ :: ys
  add0ᵣ     : x0 ≈ᴹ 0ᴹ → xs ▹ᴿ ys → xs ▹ᴿ x0 :: ys
  addedVec : x ≈ᴹ x′  → y ≈ᴹ y′
    → x :: y :: xs ▹ᴿ x′           :: y′ :: ys
    → x :: y :: xs ▹ᴿ x′ +ᴹ r *ₗ y′ :: y′ :: ys

_≈ᴿ_ = EqClosure _▹ᴿ_
_∽_ = SymClosure _▹ᴿ_

[]∽ : [] ∽ []
[]∽ = fwd []

_∷∽_ : x ≈ᴹ y → xs ∽ ys → x :: xs ∽ y :: ys
x≈y ∷∽ fwd xs∽ys = fwd (x≈y ∷ xs∽ys)
x≈y ∷∽ bwd ys∽xs = bwd (≈ᴹ-sym x≈y ∷ ys∽xs)

swap∽ : x ≈ᴹ x′ → y ≈ᴹ y′ → xs ∽ ys → x :: y :: xs ∽ y′ :: x′ :: ys
swap∽ x≈x′ y≈y′ (fwd xs∽ys) = fwd (swap x≈x′ y≈y′ xs∽ys)
swap∽ x≈x′ y≈y′ (bwd ys∽xs) = bwd (swap (≈ᴹ-sym y≈y′) (≈ᴹ-sym x≈x′) ys∽xs)

private module Example (a b : A) (r : Carrier)  where

  open StarReasoning (SymClosure _▹ᴿ_)

  _ : 0ᴹ :: [ a ] ≈ᴿ [ a ]
  _ = begin
    0ᴹ :: [ a ] ⟶⟨ bwd (add0ᵣ ≈ᴹ-refl (≈ᴹ-refl ∷ [])) ⟩
    [ a ] ∎

  _ : a ≈ᴹ b → 0ᴹ :: [ a ] ≈ᴿ [ b ]
  _ = λ a≈b → begin
    0ᴹ :: [ a ] ⟶⟨ bwd (add0ᵣ ≈ᴹ-refl (≈ᴹ-refl ∷ [])) ⟩
    [ a ] ⟶⟨ fwd (a≈b ∷ []) ⟩
    [ b ] ∎

  _ : a :: [ 0ᴹ ] ≈ᴿ [ a ]
  _ = bwd (≈ᴹ-refl ∷ add0ᵣ ≈ᴹ-refl []) ◅ ε

  _ = begin
     (a +ᴹ r *ₗ b :: [ b ]) ⟶⟨ bwd (addedVec ≈ᴹ-refl ≈ᴹ-refl (≈ᴹ-refl ∷ ≈ᴹ-refl ∷ [])) ⟩
    a :: [ b ] ∎
