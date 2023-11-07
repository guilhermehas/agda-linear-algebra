module Algebra.Instances.VecAbGroup where

open import Function
open import Data.Unit.Polymorphic
open import Data.Nat
open import Data.Vec
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Algebra

module _ {ℓ ℓ'} (GAb : AbelianGroup ℓ ℓ') where

  module AG = AbelianGroup GAb renaming (Carrier to G)
  open AG

  private
    variable
      n : ℕ

    _∙v_ : Op₂ $ Vec G n
    _∙v_ = zipWith _∙_

    εv : Vec G n
    εv = replicate _ ε

    _⁻¹v : Op₁ $ Vec G n
    _⁻¹v = map _⁻¹

    _≈v_ : Rel (Vec G n) ℓ'
    [] ≈v [] = ⊤
    (x ∷ xs) ≈v (y ∷ ys) = (x ≈ y) × (xs ≈v ys)


  open IsAbelianGroup hiding (refl)
  open IsEquivalence
  open IsGroup
  open IsMonoid
  open IsSemigroup
  open IsMagma


  IsVecAbGroup : IsAbelianGroup {A = Vec G n} _≈v_ _∙v_ εv _⁻¹v
  comm IsVecAbGroup [] [] = _
  comm IsVecAbGroup (x ∷ xs) (y ∷ ys) = AG.comm _ _ , comm IsVecAbGroup xs ys
  refl (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {[]} = _
  refl (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {x ∷ xs} =
    AG.refl , (refl (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))))
  sym (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {[]} {[]} x≡y = _
  sym (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {x ∷ xs} {y ∷ ys} (x≡y , xs≡ys) =
    AG.sym x≡y , sym (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) xs≡ys
  trans (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {[]} {[]} {[]} i≡j j≡k = _
  trans (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) {x ∷ xs} {y ∷ ys} {z ∷ zs} (x≡y , xs≡ys) (y≡z , ys≡zs) =
    (AG.trans x≡y y≡z) , trans (isEquivalence (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup))))) xs≡ys ys≡zs
  ∙-cong (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup)))) {[]} {[]} {[]} {[]} eq1 eq2 = _
  ∙-cong (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup)))) {x ∷ xs} {y ∷ ys} {u ∷ us} {v ∷ vs} (x≡y , xs≡ys) (u≡v , us≡vs) =
    (AG.∙-cong x≡y u≡v) , ∙-cong (isMagma (isSemigroup (isMonoid (isGroup IsVecAbGroup)))) xs≡ys us≡vs
  assoc (isSemigroup (isMonoid (isGroup IsVecAbGroup))) [] [] [] = _
  assoc (isSemigroup (isMonoid (isGroup IsVecAbGroup))) (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    AG.assoc x y z , assoc (isSemigroup (isMonoid (isGroup IsVecAbGroup))) xs ys zs
  proj₁ (identity (isMonoid (isGroup IsVecAbGroup))) [] = _
  proj₁ (identity (isMonoid (isGroup IsVecAbGroup))) (x ∷ xs) =
    proj₁ AG.identity x , proj₁ (identity (isMonoid (isGroup IsVecAbGroup))) xs
  proj₂ (identity (isMonoid (isGroup IsVecAbGroup))) [] = _
  proj₂ (identity (isMonoid (isGroup IsVecAbGroup))) (x ∷ xs) =
    proj₂ AG.identity x , proj₂ (identity (isMonoid (isGroup IsVecAbGroup))) xs
  proj₁ (inverse (isGroup IsVecAbGroup)) [] = _
  proj₁ (inverse (isGroup IsVecAbGroup)) (x ∷ xs) =
    proj₁ AG.inverse _ , proj₁ (inverse (isGroup IsVecAbGroup)) xs
  proj₂ (inverse (isGroup IsVecAbGroup)) [] = _
  proj₂ (inverse (isGroup IsVecAbGroup)) (x ∷ xs) =
    proj₂ AG.inverse _ , proj₂ (inverse (isGroup IsVecAbGroup)) xs
  ⁻¹-cong (isGroup IsVecAbGroup) {[]} {[]} eq = _
  ⁻¹-cong (isGroup IsVecAbGroup) {x ∷ xs} {y ∷ ys} (eqx , eqxs) =
    (AG.⁻¹-cong eqx) , ⁻¹-cong (isGroup IsVecAbGroup) eqxs

  VecAbGroup : ∀ {n} → AbelianGroup ℓ ℓ'
  VecAbGroup {n} = record
                 { Carrier = _
                 ; _≈_ = _
                 ; _∙_ = _
                 ; ε = _
                 ; _⁻¹ = _
                 ; isAbelianGroup = IsVecAbGroup {n = n}
                 }
