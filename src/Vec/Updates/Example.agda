module Vec.Updates.Example where

open import Level
open import Data.Nat using (ℕ)
open import Data.Bool
open import Data.Product
open import Data.Maybe
open import Data.Fin
open import Data.Vec as Vec hiding (_[_]≔_)
open import Data.Vec.Functional hiding (_∷_; [])
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Vec.Updates.Base
open import Vec.Relation.FirstOrNot
open import Vector

private variable
  ℓ : Level
  A : Set ℓ
  n : ℕ

open ≡-Reasoning

example : (xs : Vector A n) (i j k : Fin n) →
  (xs [ j ]≔ xs j [ i ]≔ xs i) k ≡ xs k
example xs i j k = begin
  (xs [ j ]≔ xs j [ i ]≔ xs i) k           ≡⟨ vecUpdates≡reflectBool-theo2 xs indices values k  ⟩
  evalFromPosition values (xs k) evaluated ≡⟨ helper _ (vBoolFromIndices indices k .proj₂) ⟩
  xs k ∎

  where

  indices = i ∷ j ∷ []
  values = (xs i ∷ xs j ∷ [])
  evaluated = firstTrue (proj₁ (vBoolFromIndices indices k))

  helper : ∀ vBool (vType : VecWithType (λ (ind , b) → Reflects (k ≡ ind) b) (Vec.zip indices vBool))
    → evalFromPosition values  (xs k) (firstTrue vBool) ≡ xs k
  helper (true ∷ _) (ofʸ refl ∷ _) = refl
  helper (false ∷ true ∷ vBool) (_ ∷ ofʸ refl ∷ _) = refl
  helper (false ∷ false ∷ []) _ = refl
