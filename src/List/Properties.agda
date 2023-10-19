open import Relation.Binary
open import Data.List
open import Relation.Binary.Definitions
import Data.List.Relation.Binary.Pointwise as P
import Data.List.Relation.Binary.Pointwise.Properties as P
open import Data.List.Relation.Binary.Permutation.Homogeneous as ↭ using (Permutation)

module List.Properties {ℓ} {ℓ′} {A : Set ℓ} (_≈_ : Rel A ℓ′) (ε : A) where

open import List.ZeroRel _≈_ ε as ≈₀ hiding (refl)

private variable
  0# x y : A
  xs ys zs : List A
private
  _↭_ = Permutation _≈_

refl : Reflexive _≈_ → Reflexive _≈₀_
refl ≈-refl = ≈₀.refl (P.refl ≈-refl)

sym : Symmetric _≈_ → Symmetric _≈₀_
sym ≈-sym (≈₀.refl x≈x) = ≈₀.refl (P.symmetric ≈-sym x≈x)
sym ≈-sym (prep x≈y xs≈ys) = prep (≈-sym x≈y) (sym ≈-sym xs≈ys)
sym ≈-sym (swap x≈x′ y≈y′ xs≈ys) = swap (≈-sym y≈y′) (≈-sym x≈x′) (sym ≈-sym xs≈ys)
sym ≈-sym (trans xs≈ys ys≈zs) = trans (sym ≈-sym ys≈zs) (sym ≈-sym xs≈ys)
sym ≈-sym (add0ₗ 0≈ε xs≈ys) = add0ᵣ 0≈ε (sym ≈-sym xs≈ys)
sym ≈-sym (add0ᵣ 0≈ε xs≈ys) = add0ₗ 0≈ε (sym ≈-sym xs≈ys)

cong≈₀ : x ≈ y → xs ≈₀ ys → x ∷ xs ≈₀ y ∷ ys
cong≈₀ x≈y (≈₀.refl x≈x) = ≈₀.refl (x≈y P.∷ x≈x)
cong≈₀ x≈y (prep y≈z xs≈ys) = prep x≈y (cong≈₀ y≈z xs≈ys)
cong≈₀ x≈y (swap x≈x′ y≈y′ xs≈ys) = prep x≈y (swap x≈x′ y≈y′ xs≈ys)
cong≈₀ x≈y (trans xs≈ys xs≈zs) = prep x≈y (trans xs≈ys xs≈zs)
cong≈₀ x≈y (add0ₗ 0≈ε xs≈ys) = prep x≈y (add0ₗ 0≈ε xs≈ys)
cong≈₀ x≈y (add0ᵣ 0≈ε xs≈ys) = prep x≈y (add0ᵣ 0≈ε xs≈ys)

↭→≈₀ : xs ↭ ys → xs ≈₀ ys
↭→≈₀ (↭.refl x) = ≈₀.refl x
↭→≈₀ (↭.prep eq xs↭ys) = prep eq (↭→≈₀ xs↭ys)
↭→≈₀ (↭.swap eq₁ eq₂ xs↭ys) = swap eq₁ eq₂ (↭→≈₀ xs↭ys)
↭→≈₀ (↭.trans xs↭ys xs↭ys₁) = trans (↭→≈₀ xs↭ys) (↭→≈₀ xs↭ys₁)
