open import Relation.Binary

module Vector.Setoid.Permutation.Base {a ℓ} (S : Setoid a ℓ) where

open import Level using (Level; _⊔_)
open import Data.Product
open import Relation.Binary
open import Data.Fin
open import Data.Fin.Permutation hiding (_≈_)
open import Data.Nat using (ℕ)
open import Data.Vec.Functional

open import Vector.Base
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as ≋-props

open module S = Setoid S renaming (Carrier to A) using (_≈_)
open ≋-props S

private variable
  n : ℕ
  xs ys zs : Vector A n

infix 3 _↭_

_↭_ : Rel (Vector A n) _
xs ↭ ys = Σ[ ρ ∈ Permutation′ _ ] (∀ i → xs (ρ ⟨$⟩ʳ i) ≈ ys i)
