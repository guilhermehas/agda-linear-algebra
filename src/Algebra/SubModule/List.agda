open import Level
open import Function
open import Data.Product
open import Data.List hiding (span)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Relation.Unary
open import Relation.Unary.Relation.Binary.Equality
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Algebra
open import Algebra.Module

module Algebra.SubModule.List {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  where

open Ring ring
open LeftModule leftModule renaming (Carrierᴹ to LM)
open import Algebra.SubModule.Base leftModule
open import Algebra.SubModule.Properties leftModule

open import Relation.Binary.Reasoning.Setoid (≐-setoid LM ℓm)

list→space : List LM → Cᴹ ℓm
list→space = foldr (λ v xs → (span v) +ₛ xs) 0ₛ

↭=[list→space]⇒≐ : _↭_ =[ list→space ]⇒ _≐_
↭=[list→space]⇒≐ _↭_.refl = id , id
proj₁ (↭=[list→space]⇒≐ (prep v xs↔ys)) (_ , (_ , x∈v) , y∈fold , x+y≈w)
  = (_ , _) , (_ , x∈v) , (↭=[list→space]⇒≐ xs↔ys .proj₁ y∈fold , x+y≈w)
proj₂ (↭=[list→space]⇒≐ (prep v xs↔ys)) (_ , (_ , x∈v) , y∈fold , x+y≈w)
  = (_ , _) , (_ , x∈v) , (↭=[list→space]⇒≐ xs↔ys .proj₂ y∈fold , x+y≈w)
↭=[list→space]⇒≐ (_↭_.swap {xs} {ys} x y xs↔ys) = begin
  list→space (x ∷ y ∷ xs) ≈˘⟨ +ₛ-assoc _ _ _ ⟩
  ((span x +ₛ span y) +ₛ list→space xs) ≈⟨ +ₛ-cong (+ₛ-comm _ _) (↭=[list→space]⇒≐ xs↔ys) ⟩
  ((span y +ₛ span x) +ₛ list→space ys) ≈⟨ +ₛ-assoc _ _ _ ⟩
  list→space (y ∷ x ∷ ys) ∎
↭=[list→space]⇒≐ (_↭_.trans xs↔ys ys↔zs)
  with ↭=[list→space]⇒≐ xs↔ys | ↭=[list→space]⇒≐ ys↔zs
... | f1 , f2 | f3 , f4 = f3 ∘ f1 , f2 ∘ f4
