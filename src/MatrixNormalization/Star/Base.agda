open import Algebra
open import Algebra.Module
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

open import Vec.Base

module MatrixNormalization.Star.Base {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

open Ring ring hiding (refl)
open LeftModule leftModule renaming (Carrierᴹ to A)

private variable
  n : ℕ
  i j : Fin n

infixr 4 _▹ⱽ_ _⟶ⱽ_

data _▹ⱽ_ : Rel (Vec A n) ℓr where
  swap : (xs : Vec A n) (i≢j : i ≢ j) → xs ▹ⱽ swapV xs i j
  addedVec : ∀ r (xs : Vec A n) (i≢j : i ≢ j) → xs ▹ⱽ updateAt j (r *ₗ lookup xs i +ᴹ_) xs

_⟶ⱽ_ : Rel (Vec A n) _
_⟶ⱽ_ = Star _▹ⱽ_
