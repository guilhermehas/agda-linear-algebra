open import Algebra
open import Algebra.Module
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Nullary.Decidable

open import Vec.Base
open import Vec.Permutation
import MatrixNormalization.Star.Base as MStar
open import lbry

module MatrixNormalization.Star.Properties {ℓr} {ℓr′} {ℓm} {ℓm′}
  {ring : Ring ℓr ℓr′}
  (leftModule : LeftModule ring ℓm ℓm′)
  where

open Ring ring hiding (zero)
open LeftModule leftModule renaming (Carrierᴹ to A)
open module MS = MStar leftModule
open module SR {n} = StarReasoning (_▹ⱽ_ {n})

private variable
  n : ℕ
  i j : Fin n
  x y : A
  xs ys : Vec A n

cons▹ⱽ : xs ▹ⱽ ys → x ∷ xs ▹ⱽ x ∷ ys
cons▹ⱽ (swap  _ i≢j) = swap _ (i≢j→si≢sj i≢j)
cons▹ⱽ (addedVec _ _ i≢j) = addedVec _ _ (i≢j→si≢sj i≢j)

cons⟶ⱽ : xs ⟶ⱽ ys → x ∷ xs ⟶ⱽ x ∷ ys
cons⟶ⱽ ε = ε
cons⟶ⱽ (p ◅ xs⟶ys) = cons▹ⱽ p ◅ cons⟶ⱽ xs⟶ys

↭⇒⟶ⱽ  : _↭_ ⇒ (_⟶ⱽ_ {n})
↭⇒⟶ⱽ refl = ε
↭⇒⟶ⱽ (prep x xs↭ys) = cons⟶ⱽ (↭⇒⟶ⱽ xs↭ys)
↭⇒⟶ⱽ (swap {n} {xs = xs} {ys} x y xs↭ys) = begin
  x ∷ y ∷ xs ⟶⋆⟨ cons⟶ⱽ (cons⟶ⱽ (↭⇒⟶ⱽ xs↭ys)) ⟩
  x ∷ y ∷ ys ⟶⟨ swap (x ∷ y ∷ ys) (0≢1+n {ℕ.suc n} {zero}) ⟩
  y ∷ x ∷ ys ∎
↭⇒⟶ⱽ (trans xs↭ys ys↭zs) = ↭⇒⟶ⱽ xs↭ys ◅◅ ↭⇒⟶ⱽ ys↭zs
