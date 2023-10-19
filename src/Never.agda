module Never where

open import Level using (Level)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Construct.Never
open import Relation.Nullary

module _ {a} (A : Set a) ℓ where
  impossible : ∀ {x y : A} → ¬ Never {ℓ = ℓ} x y
  impossible ()

  sym : Symmetric {A = A} {ℓ = ℓ} Never
  sym ()

  trans : Transitive {A = A} {ℓ = ℓ} Never
  trans ()

module _ a ℓ where

  trichotomous : Trichotomous {A = ⊤ {a}} _≡_ (Never {ℓ = ℓ})
  trichotomous _ _ = tri≈ (λ ()) PE.refl (λ ())

  isStrictTotalOrder : IsStrictTotalOrder {A = ⊤ {a}} _≡_ (Never {ℓ = ℓ})
  isStrictTotalOrder = record
    { isEquivalence = PE.isEquivalence
    ; trans = λ ()
    ; compare = trichotomous }

  strictTotalOrder : StrictTotalOrder _ _ _
  strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder }
