open import Level
open import Function
open import Data.Empty
open import Data.Nat using (ℕ)
open import Data.Product hiding (map)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Vec
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Pointwise.Inductive hiding (map; lookup)
  renaming (_∷_ to _::_)
open import Vec.Permutation
open import Relation.Unary
open import Relation.Unary.Properties
open import Relation.Unary.Relation.Binary.Equality
open import Relation.Binary.PropositionalEquality as ≡ hiding ([_])
open import Relation.Binary.Core
open import Algebra
open import Algebra.Module
open import Algebra.Morphism
import Algebra.Morphism.Definitions as AlgebraMor
open import Relation.Binary.Morphism.Structures

import Algebra.SubModule.Base as SMB

module Algebra.SubModule.Vec {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  (open LeftModule leftModule renaming (Carrierᴹ to LM))
  (let open SMB leftModule)
  (≈→∈ : ∀ {x y} {VS : Cᴹ ℓm} → x ≈ᴹ y → x ∈ VS → y ∈ VS)
  where

private variable
  m n : ℕ
  p : LM

Cᴹ-setoid = ≐-setoid LM ℓm

open Ring ring
open import Algebra.SubModule.SetoidProperties leftModule ≈→∈
open import Relation.Binary.Reasoning.Setoid Cᴹ-setoid
open module AMD {n} = AlgebraMor (Vec (Cᴹ ℓm) n) (Cᴹ ℓm) _≐_
open import Data.Vec.Relation.Binary.Equality.Setoid Cᴹ-setoid

vec→space' : Vec (Cᴹ ℓm) n → Cᴹ ℓm
vec→space' = foldr′ _+ₛ_ 0ₛ

vec→space : Vec LM n → Cᴹ ℓm
vec→space = vec→space' ∘ map span

isRelMorphism : IsRelHomomorphism (_≋_ {n}) _≅_ vec→space'
IsRelHomomorphism.cong isRelMorphism [] = ≐-refl
IsRelHomomorphism.cong isRelMorphism (x∼y ∷ x≡y) = +ₛ-cong x∼y (IsRelHomomorphism.cong isRelMorphism x≡y)

homo : (xs : Vec (Cᴹ ℓm) m) (ys : Vec (Cᴹ ℓm) n) → vec→space' (xs ++ ys) ≅ (vec→space' xs +ₛ vec→space' ys)
homo [] ys = ≐-sym (+ₛ-identityˡ _)
homo (x ∷ xs) ys = begin
 x +ₛ vec→space' (xs ++ ys) ≈⟨ +ₛ-congˡ (homo xs ys) ⟩
 (x +ₛ (vec→space' xs +ₛ vec→space' ys)) ≈˘⟨ +ₛ-assoc x _ _ ⟩
 ((x +ₛ vec→space' xs) +ₛ vec→space' ys) ∎

open import Algebra.Morphism.vecCommMonoid Cᴹ-setoid +ₛ-0-commutativeMonoid
  vec→space' ≐-refl isRelMorphism homo

span≐vecSpace : ∀ p → p ≅ ⦅ p ⦆
span≐vecSpace p = ≐-sym (+ₛ-identityʳ _)

private
  map-≋ : ∀ {a} {A : Set a}
    i (f : A → Cᴹ ℓm) (xs : Vec A n) p
    → map f xs [ i ]≔ f p ≋ map f (xs [ i ]≔ p)
  map-≋ Fin.zero f (x ∷ xs) p = ≐-refl :: ≋-refl
  map-≋ (Fin.suc i) f (x ∷ xs) p = ≐-refl :: (map-≋ i f xs p)

  cong-≋-[]≔ : ∀ {xs ys : Vec (Cᴹ ℓm) n} i p → xs ≋ ys
    → xs [ i ]≔ p ≋ ys [ i ]≔ p
  cong-≋-[]≔ Fin.zero p (x∼y :: eqn) = ≐-refl :: eqn
  cong-≋-[]≔ (Fin.suc i) p (x∼y :: eqn) = x∼y :: (cong-≋-[]≔ i p eqn)

swapSameVec : ∀ {xs : Vec LM n} {i j p q}
  → i ≢ j
  → (span (lookup xs i) +ₛ span (lookup xs j)) ≐ (span p +ₛ span q)
  → vec→space xs ≐ vec→space (xs [ i ]≔ p [ j ]≔ q)
swapSameVec {xs = xs} {i} {j} {p} {q} i≢j eqn = begin
  vec→space xs ≈⟨ α ⟩
  vec→space' (xs' [ i ]≔ p' [ j ]≔ q') ≈⟨ IsRelHomomorphism.cong isRelMorphism β ⟩
  vec→space' (map span (xs [ i ]≔ p [ j ]≔ q)) ∎
  where

  xs' = map span xs
  p' = span p
  q' = span q

  span-lookup : ∀ i → lookup (map span xs) i ≐ span (lookup xs i)
  span-lookup i rewrite lookup-map i span xs = ≐-refl

  ⦅⦆-eqn = begin
    (⦅ lookup xs' i ⦆ +ₛ ⦅ lookup xs' j ⦆) ≈˘⟨ +ₛ-cong (span≐vecSpace _) (span≐vecSpace _)  ⟩
    (lookup xs' i +ₛ lookup xs' j) ≈⟨ +ₛ-cong (span-lookup i) (span-lookup j) ⟩
    (span (lookup xs i) +ₛ span (lookup xs j)) ≈⟨ eqn ⟩
    (span p +ₛ span q) ≈⟨ +ₛ-cong (span≐vecSpace _) (span≐vecSpace _) ⟩
    (⦅ p' ⦆ +ₛ ⦅ q' ⦆) ∎

  α : vec→space' xs' ≐ vec→space' (xs' [ i ]≔ p' [ j ]≔ q')
  α = swapSameVecLookup {xs = xs'} i≢j ⦅⦆-eqn

  β : xs' [ i ]≔ p' [ j ]≔ q' ≋ map span (xs [ i ]≔ p [ j ]≔ q)
  β = ≋-trans (cong-≋-[]≔ j (span q) (map-≋ i span xs p)) (map-≋ j span _ q)
