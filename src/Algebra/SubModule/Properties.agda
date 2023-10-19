open import Level
open import Function
open import Data.Product
open import Relation.Unary
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Unary.Relation.Binary.Equality

module Algebra.SubModule.Properties {ℓr} {ℓm}
  {ring : Ring ℓm ℓr}
  (leftModule : LeftModule ring ℓm ℓm)
  where

open Ring ring
open LeftModule leftModule
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
open import Algebra.Solver.CommutativeMonoid +ᴹ-commutativeMonoid

_≅_ : Pred Carrierᴹ ℓm → Pred Carrierᴹ ℓm → Set _
_≅_ = _≐_

open import Algebra.Definitions _≅_
open import Algebra.Structures _≅_
open import Algebra.SubModule.Base leftModule

private variable
  ℓ ℓ′ : Level

private variable
  s₁ s₂ s₃ VS : Cᴹ ℓ
  x y : Carrierᴹ

cong-spanˡ : x ≈ᴹ y → span x ⊆ span y
proj₁ (cong-spanˡ {xs} {ys} x≈y {x} (r , _)) = r
proj₂ (cong-spanˡ {xs} {ys} x≈y {x} (r , x∈xs)) = begin
  r *ₗ ys ≈˘⟨ *ₗ-congˡ x≈y ⟩
  r *ₗ xs ≈⟨ x∈xs ⟩
  x ∎

cong-spanʳ : x ≈ᴹ y → span x ⊇ span y
cong-spanʳ = cong-spanˡ ∘ ≈ᴹ-sym

cong-span : x ≈ᴹ y → span x ≐ span y
cong-span x≈y = cong-spanˡ x≈y , cong-spanʳ x≈y

-- Algebraic properties of _+ₛ_

+ₛ-cong : Congruent₂ _+ₛ_
proj₁ (+ₛ-cong {xs} {ys} {zs} (x⊆y , y⊆x) (u⊆v , v⊆u)) {yv} ((a , b) , a∈xs , b∈zs , a+b≈yv) =
  (_ , _) , x⊆y a∈xs , u⊆v b∈zs , a+b≈yv
proj₂ (+ₛ-cong {xs} {ys} {zs} (x⊆y , y⊆x) (u⊆v , v⊆u)) {yv} ((a , b) , a∈xs , b∈zs , a+b≈yv) =
  (_ , _) , y⊆x a∈xs , v⊆u b∈zs , a+b≈yv

+ₛ-congˡ : LeftCongruent _+ₛ_
proj₁ (+ₛ-congˡ {xs} {ys} {zs} (ys⊆zs , ys⊇zs)) ((a , b) , a∈xs , b∈zs , a+b≈x) =
  (_ , _) , a∈xs , ys⊆zs b∈zs , a+b≈x
proj₂ (+ₛ-congˡ {xs} {ys} {zs} (ys⊆zs , ys⊇zs)) ((a , b) , a∈xs , b∈ys , a+b≈x) =
  (_ , _) , a∈xs , ys⊇zs b∈ys , a+b≈x

+ₛ-congʳ : RightCongruent _+ₛ_
proj₁ (+ₛ-congʳ {xs} {ys} {zs} (ys⊆zs , ys⊇zs)) ((a , b) , a∈zs , b∈xs , a+b≈x) =
  (_ , _) , ys⊆zs a∈zs , b∈xs , a+b≈x
proj₂ (+ₛ-congʳ {xs} {ys} {zs} (ys⊆zs , ys⊇zs)) ((a , b) , a∈ys , b∈xs , a+b≈x) =
  (_ , _) , ys⊇zs a∈ys , b∈xs , a+b≈x

+ₛ-assoc : Associative _+ₛ_
proj₁ (+ₛ-assoc xs ys zs) {xyz} ((xy , z) , ((x , y) , x∈xs , y∈ys , x+y≈xy) , z∈zs , xy+z≈xyz) =
  (x , y +ᴹ z) , x∈xs , ((y , z) , y∈ys , z∈zs , ≈ᴹ-refl) , (begin
    x +ᴹ (y +ᴹ z) ≈˘⟨ +ᴹ-assoc x y z ⟩
    x +ᴹ y +ᴹ z    ≈⟨ +ᴹ-congʳ x+y≈xy ⟩
    xy +ᴹ z        ≈⟨ xy+z≈xyz ⟩
    xyz ∎)
proj₂ (+ₛ-assoc xs ys zs) {xyz} ((x , yz) , x∈xs , ((y , z) , y∈ys , z∈zs , y+z≈yz) , x+yz≈xyz) =
  ((x +ᴹ y) , z) , ((x , y) , x∈xs , y∈ys , ≈ᴹ-refl) , z∈zs , (begin
    x +ᴹ y +ᴹ z   ≈⟨ +ᴹ-assoc x y z ⟩
    x +ᴹ (y +ᴹ z) ≈⟨ +ᴹ-congˡ y+z≈yz ⟩
    x +ᴹ yz       ≈⟨ x+yz≈xyz ⟩
    xyz ∎)

+ₛ-comm : Commutative _+ₛ_
proj₁ (+ₛ-comm xs ys) {z} ((x , y) , x∈xs , y∈ys , x+y≈z) = (y , x) , y∈ys , x∈xs ,
  ≈ᴹ-trans (+ᴹ-comm y x) x+y≈z
proj₂ (+ₛ-comm xs ys) {z} ((x , y) , x∈xs , y∈ys , x+y≈z) = (y , x) , y∈ys , x∈xs ,
  ≈ᴹ-trans (+ᴹ-comm y x) x+y≈z

-- Structures

+ₛ-isMagma : IsMagma _+ₛ_
+ₛ-isMagma = record
  { isEquivalence = ≐-isEquivalence
  ; ∙-cong = +ₛ-cong
  }

+ₛ-isSemigroup : IsSemigroup _+ₛ_
+ₛ-isSemigroup = record
  { isMagma = +ₛ-isMagma
  ; assoc = +ₛ-assoc
  }

+ₛ-isCommutativeSemigroup : IsCommutativeSemigroup _+ₛ_
+ₛ-isCommutativeSemigroup = record
  { isSemigroup = +ₛ-isSemigroup
  ; comm = +ₛ-comm
  }

-- Bundles

+ₛ-magma : Magma _ _
+ₛ-magma = record
  {isMagma = +ₛ-isMagma
  }

+ₛ-semigroup : Semigroup _ _
+ₛ-semigroup = record
  { isSemigroup = +ₛ-isSemigroup
  }

+ₛ-commutativeSemigroup : CommutativeSemigroup _ _
+ₛ-commutativeSemigroup = record
  { isCommutativeSemigroup = +ₛ-isCommutativeSemigroup
  }


-- Other properties

sameMultipliedʳ : ∀ r v → span v ⊇ span (r *ₗ v)
sameMultipliedʳ r v {x} (r₂ , rs) = r₂ * r , (begin
  (r₂ * r) *ₗ v ≈⟨ *ₗ-assoc _ _ _ ⟩
  r₂ *ₗ r  *ₗ v ≈⟨ rs ⟩
  x ∎)

sameAdd : ∀ r v₁ v₂ → (span v₁ +ₛ span (r *ₗ v₁ +ᴹ v₂)) ≐ (span v₁ +ₛ span v₂)
proj₁ (sameAdd r v₁ v₂) {yz} ((y , z) , (r₁ , r₁*v₁≈y) , (r₂ , r₂*v≈z) , y+z≈yz) =
  ((r₁ + r₂ * r) *ₗ v₁ , r₂ *ₗ v₂) , (r₁ + r₂ * r , ≈ᴹ-refl) , (r₂ , ≈ᴹ-refl) , (begin

    (r₁ + r₂ * r) *ₗ v₁ +ᴹ r₂ *ₗ v₂          ≈⟨ +ᴹ-congʳ (*ₗ-distribʳ v₁ r₁ _) ⟩
    r₁ *ₗ v₁ +ᴹ (r₂ * r) *ₗ v₁ +ᴹ r₂ *ₗ v₂   ≈⟨ +ᴹ-assoc _ _ _ ⟩
    r₁ *ₗ v₁ +ᴹ ((r₂ * r) *ₗ v₁ +ᴹ r₂ *ₗ v₂) ≈⟨ +ᴹ-congˡ (+ᴹ-congʳ (*ₗ-assoc _ _ _)) ⟩
    r₁ *ₗ v₁ +ᴹ (r₂ *ₗ r *ₗ v₁ +ᴹ r₂ *ₗ v₂) ≈˘⟨ +ᴹ-congˡ (*ₗ-distribˡ _ _ _) ⟩
    r₁ *ₗ v₁ +ᴹ r₂ *ₗ (r *ₗ v₁ +ᴹ v₂)        ≈⟨ +ᴹ-cong r₁*v₁≈y r₂*v≈z ⟩
    y +ᴹ z ≈⟨ y+z≈yz ⟩
    yz ∎)
proj₂ (sameAdd r v₁ v₂) {yz} ((y , z) , (r₁ , r₁*v₁≈y) , (r₂ , r₂*v₂≈z) , y+z≈yz) =
  (((r₁ - r₂ * r) *ₗ v₁) , (r₂ *ₗ _)) , (_ , ≈ᴹ-refl) , (_ , ≈ᴹ-refl) , (begin

    (r₁ - r₂ * r) *ₗ v₁ +ᴹ r₂ *ₗ (r *ₗ v₁ +ᴹ v₂)                 ≈⟨ +ᴹ-congˡ (*ₗ-distribˡ _ _ _) ⟩
    (r₁ - r₂ * r) *ₗ v₁ +ᴹ (r₂ *ₗ r *ₗ v₁ +ᴹ r₂ *ₗ v₂)           ≈⟨ +ᴹ-congʳ (*ₗ-distribʳ _ _ _) ⟩
    r₁ *ₗ v₁ +ᴹ - (r₂ * r) *ₗ v₁ +ᴹ (r₂ *ₗ r *ₗ v₁ +ᴹ r₂ *ₗ v₂) ≈˘⟨ +ᴹ-congˡ (+ᴹ-congʳ (*ₗ-assoc _ _ _)) ⟩
    r₁ *ₗ v₁ +ᴹ - (r₂ * r) *ₗ v₁ +ᴹ ((r₂ * r) *ₗ v₁ +ᴹ r₂ *ₗ v₂) ≈⟨ lemma₂ _ _ _ _ ⟩
    r₁ *ₗ v₁ +ᴹ r₂ *ₗ v₂                                         ≈⟨ +ᴹ-cong r₁*v₁≈y r₂*v₂≈z ⟩
    y +ᴹ z                                                       ≈⟨ y+z≈yz ⟩
    yz ∎) where

    lemma : ∀ x y w z → x +ᴹ y +ᴹ (w +ᴹ z) ≈ᴹ w +ᴹ y +ᴹ x +ᴹ z
    lemma = solve 4 (λ x y w z → (x ⊕ y) ⊕ w ⊕ z , ((w ⊕ y) ⊕ x) ⊕ z) ≈ᴹ-refl

    lemma-inv : ∀ r v → r *ₗ v +ᴹ (- r) *ₗ v ≈ᴹ 0ᴹ
    lemma-inv r v = begin
      r *ₗ v +ᴹ (- r) *ₗ v ≈˘⟨ *ₗ-distribʳ _ _ _ ⟩
      (r + (- r)) *ₗ v      ≈⟨ *ₗ-congʳ (-‿inverseʳ _) ⟩
      0# *ₗ v               ≈⟨ *ₗ-zeroˡ _ ⟩
      0ᴹ ∎

    lemma₂ : ∀ r x y z → x +ᴹ - r *ₗ y +ᴹ (r *ₗ y +ᴹ z) ≈ᴹ x +ᴹ z
    lemma₂ r x y z = begin
      x +ᴹ _ +ᴹ (_ +ᴹ z) ≈⟨ lemma x _ _ z ⟩
      _ +ᴹ _ +ᴹ x +ᴹ z   ≈⟨ +ᴹ-congʳ (+ᴹ-congʳ (lemma-inv _ _)) ⟩
      0ᴹ +ᴹ x +ᴹ z       ≈⟨ +ᴹ-congʳ (+ᴹ-identityˡ _) ⟩
      x +ᴹ z ∎

-→-ᴹ : ∀ r xs → - r *ₗ xs ≈ᴹ -ᴹ (r *ₗ xs)
-→-ᴹ r xs = uniqueˡ‿-ᴹ _ _ (begin
  - r *ₗ xs +ᴹ r *ₗ xs ≈˘⟨ *ₗ-distribʳ _ _ _ ⟩
  (- r + r) *ₗ xs ≈⟨ *ₗ-congʳ (-‿inverseˡ _) ⟩
  0# *ₗ xs ≈⟨ *ₗ-zeroˡ _ ⟩
  0ᴹ ∎)
