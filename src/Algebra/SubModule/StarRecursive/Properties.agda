open import Function
open import Algebra.Bundles
open import Algebra.Module
open import Data.List renaming (_∷_ to _::_)
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
import Data.List.Relation.Binary.Permutation.Setoid.Properties as ↭Properties
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.Construct.Closure.Equivalence as E
open import Relation.Binary.Construct.Closure.Symmetric as S

import Algebra.SubModule.StarRecursive.Base as SubModuleBase

module Algebra.SubModule.StarRecursive.Properties {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

open Ring ring
open LeftModule leftModule renaming (Carrierᴹ to A)
open SubModuleBase leftModule
open StarReasoning (SymClosure _▹ᴿ_)
open Equality ≈ᴹ-setoid
open Permutation ≈ᴹ-setoid
open ↭Properties ≈ᴹ-setoid

private variable
  x y x′ y′ : A
  xs ys xs′ ys′ : List A


≋⇒▹ᴿ : _≋_ ⇒ _▹ᴿ_
≋⇒▹ᴿ [] = []
≋⇒▹ᴿ (x∼y ∷ xs≋ys) = x∼y ∷ ≋⇒▹ᴿ xs≋ys

▹ᴿ-refl : Reflexive _▹ᴿ_
▹ᴿ-refl = ≋⇒▹ᴿ ≋-refl

≋⇒≈ᴿ : _≋_ ⇒ _≈ᴿ_
≋⇒≈ᴿ = E.return ∘ ≋⇒▹ᴿ

cons-≈ᴿ : x ≈ᴹ y → xs ≈ᴿ ys → x :: xs ≈ᴿ y :: ys
cons-≈ᴿ x≈y ε = E.return (x≈y ∷ ▹ᴿ-refl)
cons-≈ᴿ x≈y (p ◅ xs≈ys) = (x≈y ∷∽ p) ◅ cons-≈ᴿ ≈ᴹ-refl xs≈ys

cons≡-≈ᴿ : xs ≈ᴿ ys → x :: xs ≈ᴿ x :: ys
cons≡-≈ᴿ = cons-≈ᴿ ≈ᴹ-refl

swap-≈ᴿ : x ≈ᴹ x′ → y ≈ᴹ y′ → xs ≈ᴿ ys → x :: y :: xs ≈ᴿ y′ :: x′ :: ys
swap-≈ᴿ x≈x′ y≈y′ ε = E.return (swap x≈x′ y≈y′ ▹ᴿ-refl)
swap-≈ᴿ x≈x′ y≈y′ (p ◅ xs≈ys) = swap∽ x≈x′ y≈y′ p ◅ cons≡-≈ᴿ (cons≡-≈ᴿ xs≈ys)

↭⇒≈ᴿ : _↭_ ⇒ _≈ᴿ_
↭⇒≈ᴿ (refl x) = ≋⇒≈ᴿ x
↭⇒≈ᴿ (prep eq xs⇹ys) = cons-≈ᴿ eq (↭⇒≈ᴿ xs⇹ys)
↭⇒≈ᴿ (swap eq₁ eq₂ xs⇹ys) = swap-≈ᴿ eq₁ eq₂ (↭⇒≈ᴿ xs⇹ys)
↭⇒≈ᴿ (trans xs⇹ys ys⇹zs) = ↭⇒≈ᴿ xs⇹ys ◅◅ ↭⇒≈ᴿ ys⇹zs

≈ᴿ-respʳ-↭ : _≈ᴿ_ Respectsʳ _↭_
≈ᴿ-respʳ-↭ {xs} {ys} {zs} ys↭zs xs≈ys = begin
  xs ⟶⋆⟨ xs≈ys ⟩
  ys ⟶⋆⟨ ↭⇒≈ᴿ ys↭zs ⟩
  zs ∎

≈ᴿ-respˡ-↭ : _≈ᴿ_ Respectsʳ _↭_
≈ᴿ-respˡ-↭ {xs} {ys} {zs} ys↭zs xs≈ys = begin
  xs ⟶⋆⟨ xs≈ys ⟩
  ys ⟶⋆⟨ ↭⇒≈ᴿ ys↭zs ⟩
  zs ∎

++ₗ→∽ : ys ∽ ys′ → xs ++ ys ≈ᴿ xs ++ ys′
++ₗ→∽ {xs = []} = RT.return
++ₗ→∽ {xs = _ :: _} = cons≡-≈ᴿ ∘ ++ₗ→∽

++→∽ : xs ∽ xs′ → xs ++ ys ≈ᴿ xs′ ++ ys
++→∽ {xs} {xs′} {ys} xs∽xs′ = begin
  xs ++ ys  ⟶⋆⟨ ↭⇒≈ᴿ (++-comm xs ys) ⟩
  ys ++ xs  ⟶⋆⟨ ++ₗ→∽ xs∽xs′ ⟩
  ys ++ xs′ ⟶⋆⟨ ↭⇒≈ᴿ (++-comm ys xs′) ⟩
  xs′ ++ ys ∎

++→≈ᴹ : xs ≈ᴿ xs′ → ys ≈ᴿ ys′ → xs ++ ys ≈ᴿ xs′ ++ ys′
++→≈ᴹ {[]} ε = id
++→≈ᴹ {_ :: _} ε = cons≡-≈ᴿ ∘ ++→≈ᴹ ε
++→≈ᴹ (p ◅ xs≈xs′) ys≈ys′ = ++→∽ p ◅◅ ++→≈ᴹ xs≈xs′ ys≈ys′
