module Vector.Permutation.Base where

open import Level
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Fin.Permutation
open import Data.Vec.Functional
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous.Core using (IRel)
open import Relation.Binary.PropositionalEquality


private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ
  xs ys : Vector A n

infix 3 _↭_

_↭_ : IRel (Vector A) _
xs ↭ ys = Σ[ ρ ∈ Permutation _ _ ] (∀ i → xs (ρ ⟨$⟩ʳ i) ≡ ys i)

_↭′_ : Rel (Vector A n) _
_↭′_ = _↭_
