module Vec.Updates where

open import Level
open import Function
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec as Vec hiding (_[_]≔_)
open import Data.Vec.Functional using (Vector; fromVec)
open import Data.Vec.Functional.Properties
open import Relation.Binary.PropositionalEquality
open import Vec.Relation.FirstOrNot
open import Relation.Nullary

open import Vector

private variable
  ℓ : Level
  A : Set ℓ
  a : A
  m n : ℕ
  b : Bool
  xs : Vec A n

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

evalFromPosition : (values : Vec A n) (default : A) (pos : Maybe $ Fin n) → A
evalFromPosition = maybe′ ∘ fromVec

firstOrNot→pos : (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) (i : Fin n)
  (firstOrNot : FirstOrNot (i ≡_) indices b) → A
firstOrNot→pos xs values i = evalFromPosition values (xs i) ∘ firstOrNotPositionMaybe

data VecWithType (P : A → Set ℓ) : Vec A n → Set ℓ where
  []  : VecWithType P []
  _∷_ : P a → VecWithType P xs → VecWithType P (a ∷ xs)


evalFromVReflect : (xs : Vector A n) {vBool : Vec Bool m}
  (values : Vec A m) (i : Fin n) (firstOrNot : FirstOrNot T vBool b) → A
evalFromVReflect xs values i firstOrNot = evalFromPosition values
  (xs i) (firstOrNotPositionMaybe firstOrNot)

evalFromVReflect¬≡ :  ∀ (xs : Vector A n) {vBool : Vec Bool m}
  (values : Vec A m) (i : Fin n) (firstOrNot : FirstOrNot T vBool b) val →
  evalFromVReflect xs (val ∷ values) i (there id firstOrNot)
  ≡ evalFromVReflect xs values i firstOrNot
evalFromVReflect¬≡ {b = false} xs values i firstOrNot val = refl
evalFromVReflect¬≡ {b = true} xs values i firstOrNot val = refl


vecUpdates≡reflectBool : ∀ (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) i
  {vBool : Vec Bool m} (vType : VecWithType (λ (ind , b) → Reflects (i ≡ ind) b) (Vec.zip indices vBool))
  (firstOrNot : FirstOrNot T vBool b)
  → vecUpdates xs indices values i ≡ evalFromVReflect xs values i firstOrNot
vecUpdates≡reflectBool xs {[]} [] i vType notHere = refl
vecUpdates≡reflectBool xs {ind ∷ indices} (val ∷ values) _ (ofʸ refl ∷ vType) (here _ vBool) = updateAt-updates ind _
vecUpdates≡reflectBool xs {ind ∷ indices} (val ∷ values) _ (ofʸ refl ∷ vType) (there ¬p firstOrNot) with () ← ¬p _
vecUpdates≡reflectBool xs {ind ∷ indices} (val ∷ values) i (ofⁿ ¬i≡ind ∷ vType) (there ¬p firstOrNot) = begin
  (vecUpdates xs indices values [ ind ]≔ val) i ≡⟨ updateAt-minimal i _ _ ¬i≡ind ⟩
  vecUpdates xs indices values i                ≡⟨ vecUpdates≡reflectBool xs values i vType firstOrNot ⟩
  evalFromVReflect xs values i firstOrNot      ≡˘⟨ evalFromVReflect¬≡ xs values i firstOrNot val ⟩
  evalFromVReflect xs (val ∷ values) i (there ¬p firstOrNot) ∎
