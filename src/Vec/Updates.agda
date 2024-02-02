module Vec.Updates where

open import Level
open import Function
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_[_]≔_)
open import Data.Vec.Functional using (Vector)
open import Data.Vec.Functional.Properties
open import Relation.Binary.PropositionalEquality
open import Vec.Relation.FirstOrNot

open import Vector

private variable
  ℓ : Level
  A : Set ℓ
  m n : ℕ
  b : Bool

open ≡-Reasoning

evalFromListUpdates : (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) (i : Fin n)
  (firstOrNot : FirstOrNot (i ≡_) indices b) → A
evalFromListUpdates xs values i (there _ firstOrNot) =
  evalFromListUpdates xs (tail values) i firstOrNot
evalFromListUpdates {b = false} xs values i firstOrNot = xs i
evalFromListUpdates {b = true} xs (x ∷ values) i (here _ _) = x

vecUpdates : (xs : Vector A n) (indices : Vec (Fin n) m) (values : Vec A m) → Vector A n
vecUpdates xs [] [] = xs
vecUpdates xs (ind ∷ indices) (val ∷ values) = vecUpdates xs indices values [ ind ]≔ val

vecUpdates≡listUpdates : ∀ (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) i
  (firstOrNot : FirstOrNot (i ≡_) indices b)
  → vecUpdates xs indices values i ≡ evalFromListUpdates xs values i firstOrNot
vecUpdates≡listUpdates xs [] i notHere = refl
vecUpdates≡listUpdates xs {.(i ∷ _)} (_ ∷ values) i (here refl _) = updateAt-updates i _
vecUpdates≡listUpdates xs {ind ∷ inds} (val ∷ values) i (there ¬p firstOrNot) = begin
  (vecUpdates xs inds values [ ind ]≔ val) i ≡⟨ updateAt-minimal _ _ _ ¬p ⟩
  vecUpdates xs inds values i                ≡⟨ vecUpdates≡listUpdates xs values i firstOrNot ⟩
  evalFromListUpdates xs (val ∷ values) i (there ¬p firstOrNot) ∎
