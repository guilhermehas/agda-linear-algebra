module Vec.Updates.Base where

open import Level
open import Function
open import Data.Empty
open import Data.Bool
open import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Data.Product
open import Data.Nat hiding (less-than-or-equal)
open import Data.Fin as Fin
open import Data.Vec as Vec hiding (_[_]≔_)
import Data.Vec.Properties as Vec
open import Data.Vec.Functional using (Vector; fromVec)
open import Data.Vec.Functional.Properties using (updateAt-updates; updateAt-minimal)
open import Relation.Binary.PropositionalEquality
open import Vec.Relation.FirstOrNot
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary

open import Vector

private variable
  ℓ ℓ1 : Level
  A : Set ℓ
  a : A
  m n p q : ℕ
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

infixr 5 _∷_

data VecWithType {A : Set ℓ} (P : A → Set ℓ1) : Vec A n → Set (ℓ Level.⊔ ℓ1) where
  []  : VecWithType P []
  _∷_ : P a → VecWithType P xs → VecWithType P (a ∷ xs)

VecIndBool : ∀ (indices : Vec A n) vBool k → Set _
VecIndBool indices vBool k = VecWithType (λ (ind , b) → Reflects (k ≡ ind) b) $ Vec.zip indices vBool

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

vecUpdates≡reflectBool-lema₂ : ∀ (xs : Vector A n) (values : Vec A m) (vBool : Vec Bool m) →
  firstOrNotPositionMaybe (proj₂ (firstOrNotFromDec T? vBool)) ≡ firstTrue vBool
vecUpdates≡reflectBool-lema₂ xs [] [] = refl
vecUpdates≡reflectBool-lema₂ xs (x ∷ values) (true ∷ vBool) = refl
vecUpdates≡reflectBool-lema₂ xs (x ∷ values) (false ∷ vBool)
  rewrite sym $ vecUpdates≡reflectBool-lema₂ xs values vBool
  with firstOrNotFromDec T? vBool in eq
... | true , _ = refl
... | false , _ = refl

vecUpdates≡reflectBool-lemma : ∀ (xs : Vector A n) (values : Vec A m) i (vBool : Vec Bool m) →
  evalFromPosition values (xs i) (firstOrNotPositionMaybe $ proj₂ (firstOrNotFromDec T? vBool)) ≡
  evalFromPosition values (xs i) (firstTrue vBool)
vecUpdates≡reflectBool-lemma xs values i vBool rewrite vecUpdates≡reflectBool-lema₂ xs values vBool = refl

vecUpdates≡reflectBool-theo : ∀ (xs : Vector A n) {indices : Vec (Fin n) m} (values : Vec A m) i
  {vBool : Vec Bool m} (vType : VecIndBool indices vBool i)
  → vecUpdates xs indices values i ≡ evalFromPosition values (xs i) (firstTrue vBool)
vecUpdates≡reflectBool-theo xs {indices} values i {vBool} vType = begin
  vecUpdates xs indices values i ≡⟨ vecUpdates≡reflectBool xs values i vType (proj₂ (firstOrNotFromDec T? vBool)) ⟩
  evalFromVReflect xs values i (proj₂ (firstOrNotFromDec T? vBool)) ≡⟨ vecUpdates≡reflectBool-lemma xs values i vBool ⟩
  evalFromPosition values (xs i) (firstTrue vBool) ∎

vBoolFromIndices : ∀ (indices : Vec (Fin n) m) (i : Fin n) → Σ[ vBool ∈ Vec Bool m ]
  VecWithType (λ (ind , b) → Reflects (i ≡ ind) b) (Vec.zip indices vBool)
vBoolFromIndices [] i = [] , []
vBoolFromIndices (ind ∷ indices) i = _ , proof (i Fin.≟ ind) ∷ proj₂ (vBoolFromIndices indices i)

vecUpdates≡reflectBool-theo2 : ∀ (xs : Vector A n) (indices : Vec (Fin n) m) (values : Vec A m) i
  → vecUpdates xs indices values i ≡ evalFromPosition values (xs i) (firstTrue (vBoolFromIndices indices i .proj₁))
vecUpdates≡reflectBool-theo2 xs indices values i = vecUpdates≡reflectBool-theo xs values i (proj₂ (vBoolFromIndices indices i))

vecUpdates≡reflectBool-lemma3 : ∀ (indices : Vec (Fin n) m) i
  {vBool : Vec Bool m} (vType : VecIndBool indices vBool i)
  → vBoolFromIndices indices i .proj₁ ≡ vBool
vecUpdates≡reflectBool-lemma3 [] i {[]} vType = refl
vecUpdates≡reflectBool-lemma3 (ind ∷ indices) i {false ∷ vBool} (ofⁿ ¬a ∷ vType) =
  cong₂ _∷_ (dec-false (_ Fin.≟ _) ¬a) (vecUpdates≡reflectBool-lemma3 indices _ vType)
vecUpdates≡reflectBool-lemma3 (ind ∷ indices) _ {true ∷ vBool} (ofʸ refl ∷ vType)
   = cong₂ _∷_ (dec-true (ind Fin.≟ ind) refl) (vecUpdates≡reflectBool-lemma3 indices _ vType)

vecUpdates≡reflectBool-theo3 : ∀ (xs : Vector A n) (indices : Vec (Fin n) m) (values : Vec A m) i
  {vBool : Vec Bool m} (vType : VecIndBool indices vBool i)
  → evalFromPosition values (xs i) (firstTrue (vBoolFromIndices indices i .proj₁))
  ≡ evalFromPosition values (xs i) (firstTrue vBool)
vecUpdates≡reflectBool-theo3 xs indices values i vType
  rewrite vecUpdates≡reflectBool-lemma3 indices i vType = refl
