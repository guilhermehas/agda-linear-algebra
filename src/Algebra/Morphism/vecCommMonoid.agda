open import Data.Empty
open import Data.Nat using (ℕ; _+_)
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Vec
open import Algebra
import Algebra.Morphism.Definitions as MorphDefs
open import Relation.Binary
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.PropositionalEquality as ≡ using (_≢_)
import Data.Vec.Relation.Binary.Equality.Setoid as VecSetoid

open import Vec.Permutation

module Algebra.Morphism.vecCommMonoid {c} {ℓ} {a} {ℓ′}
  (S : Setoid a ℓ′)
  (let open module S = Setoid S renaming (Carrier to A; _≈_ to _≈₁_))
  (open VecSetoid S)
  (cMonoid : CommutativeMonoid c ℓ)
  (let open module CM = CommutativeMonoid cMonoid renaming (Carrier to B; _≈_ to _≈₂_))
  (let open module MD {n} = MorphDefs (Vec A n) B _≈₂_)
  (⟦_⟧ : ∀ {n} → Vec A n → B)
  (ε-homo : Homomorphic₀ ⟦_⟧ [] ε)
  (isRelHomomorphism : ∀ {n} → IsRelHomomorphism (_≋_ {n}) _≈₂_ ⟦_⟧)
  (homo : ∀ {m n} → (xs : Vec A m) (ys : Vec A n) → ⟦ xs ++ ys ⟧ ≈₂ ⟦ xs ⟧ ∙ ⟦ ys ⟧)
  where

open module IRL {n} = IsRelHomomorphism (isRelHomomorphism {n})

open import Vec.View S
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Solver.CommutativeMonoid cMonoid hiding (⟦_⟧)

private variable
  m n : ℕ
  xs ys ws zs vs : Vec A n
  p q : A
  x y w z v : B

⦅_⦆ : A → B
⦅ x ⦆ = ⟦ [ x ] ⟧

↭⇒≈ : (_↭_ {n = n}) =[ ⟦_⟧ ]⇒ _≈₂_
↭⇒≈ _↭_.refl = CM.refl
↭⇒≈ (prep {n} {xs} {ys} x xs↔ys) = begin
  ⟦ [ x ] ++  xs ⟧ ≈⟨ homo _ _ ⟩
  ⦅ x ⦆ ∙ ⟦ xs ⟧   ≈⟨ ∙-congˡ (↭⇒≈ xs↔ys) ⟩
  ⦅ x ⦆ ∙ ⟦ ys ⟧  ≈˘⟨ homo _ _ ⟩
  ⟦ [ x ] ++ ys ⟧   ∎
↭⇒≈ (swap {n} {xs} {ys} x y xs↔ys) = begin
  ⟦ [ x ] ++ [ y ] ++ xs ⟧  ≈⟨ homo _ _ ⟩
  ⦅ x ⦆ ∙ ⟦ [ y ] ++ xs ⟧   ≈⟨ ∙-congˡ (homo _ _) ⟩
  ⦅ x ⦆ ∙ (⦅ y ⦆ ∙ ⟦ xs ⟧) ≈˘⟨ assoc _ _ _ ⟩
  ⦅ x ⦆ ∙ ⦅ y ⦆ ∙ ⟦ xs ⟧    ≈⟨ ∙-cong (comm _ _) (↭⇒≈ xs↔ys) ⟩
  ⦅ y ⦆ ∙ ⦅ x ⦆ ∙ ⟦ ys ⟧    ≈⟨ assoc _ _ _ ⟩
  ⦅ y ⦆ ∙ (⦅ x ⦆ ∙ ⟦ ys ⟧) ≈˘⟨ ∙-congˡ (homo _ _) ⟩
  ⦅ y ⦆ ∙ ⟦ [ x ] ++ ys ⟧  ≈˘⟨ homo _ _ ⟩
  ⟦ [ y ] ++ [ x ] ++ ys ⟧   ∎
↭⇒≈ (_↭_.trans {n} {xs} {ys} {zs} xs↔ys ys↔zs) = begin
  ⟦ xs ⟧ ≈⟨ ↭⇒≈ xs↔ys ⟩
  ⟦ ys ⟧ ≈⟨ ↭⇒≈ ys↔zs ⟩
  ⟦ zs ⟧ ∎

cong-vec : {xs : Vec A m} {ys : Vec A n} → xs ≋ ys → ⟦ xs ⟧ ≈₂ ⟦ ys ⟧
cong-vec eqn with length-equal eqn
... | ≡.refl = cong eqn

cong-⦅⦆ : p ≈₁ q → ⦅ p ⦆ ≈₂ ⦅ q ⦆
cong-⦅⦆ eqn = cong (eqn VecSetoid.∷ VecSetoid.[])

homo5 : ⟦ xs ++ ys ++ ws ++ zs ++ vs ⟧ ≈₂ ⟦ xs ⟧ ∙ (⟦ ys ⟧ ∙ (⟦ ws ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ vs ⟧)))
homo5 {xs = xs} {ys = ys} {ws = ws} {zs = zs} {vs = vs} = begin
 ⟦ xs ++ ys ++ ws ++ zs ++ vs ⟧ ≈⟨ homo xs _ ⟩
 ⟦ xs ⟧ ∙  ⟦ ys ++ ws ++ zs ++ vs ⟧ ≈⟨ ∙-congˡ (homo ys _) ⟩
 ⟦ xs ⟧ ∙ (⟦ ys ⟧ ∙ ⟦ ws ++ zs ++ vs ⟧) ≈⟨ ∙-congˡ (∙-congˡ (homo ws _)) ⟩
 ⟦ xs ⟧ ∙ (⟦ ys ⟧ ∙ (⟦ ws ⟧ ∙ ⟦ zs ++ vs ⟧)) ≈⟨ ∙-congˡ (∙-congˡ (∙-congˡ (homo _ _))) ⟩
 ⟦ xs ⟧ ∙ (⟦ ys ⟧ ∙ (⟦ ws ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ vs ⟧))) ∎


swap5 : x ∙ (y ∙ (w ∙ (z ∙ v))) ≈₂ (y ∙ z) ∙ (x ∙ (w ∙ v))
swap5 = solve 5 (λ x y w z v → x ⊕ (y ⊕ (w ⊕ (z ⊕ v))) ⊜ (y ⊕ z) ⊕ (x ⊕ (w ⊕ v))) CM.refl _ _ _ _ _

swap5' : x ∙ (y ∙ (w ∙ (z ∙ v))) ≈₂ (z ∙ y) ∙ (x ∙ (w ∙ v))
swap5' = solve 5 (λ x y w z v → x ⊕ (y ⊕ (w ⊕ (z ⊕ v))) ⊜ (z ⊕ y) ⊕ (x ⊕ (w ⊕ v))) CM.refl _ _ _ _ _

swapSameVecI<j : ∀ {xs : Vec A (2 + n)} {i j p q}
  → i < j
  → ⦅ lookup xs i ⦆ ∙ ⦅ lookup xs j ⦆ ≈₂ ⦅ p ⦆ ∙ ⦅ q ⦆
  → ⟦ xs ⟧ ≈₂ ⟦ xs [ i ]≔ p [ j ]≔ q ⟧
swapSameVecI<j {xs = xs} {i} {j} {p} {q} i<j eqn with vec→VecView2 xs i<j
... | view2 {ys = ys} {x} {zs} {w} {ws} vec≡xs = begin
  ⟦ xs ⟧ ≈˘⟨ cong-vec vec≡xs ⟩
  ⟦ ys ++ [ x ] ++ zs ++ [ w ] ++ ws ⟧ ≈⟨ homo5 ⟩
  ⟦ ys ⟧ ∙ (⦅ x ⦆ ∙ (⟦ zs ⟧ ∙ (⦅ w ⦆ ∙ ⟦ ws ⟧))) ≈⟨ swap5 ⟩
  ⦅ x ⦆ ∙ ⦅ w ⦆ ∙ (⟦ ys ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ ws ⟧)) ≈⟨ ∙-congʳ xw≡pq ⟩
  ⦅ p ⦆ ∙ ⦅ q ⦆ ∙ (⟦ ys ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ ws ⟧)) ≈˘⟨ swap5 ⟩
  ⟦ ys ⟧ ∙ (⦅ p ⦆ ∙ (⟦ zs ⟧ ∙ (⦅ q ⦆ ∙ ⟦ ws ⟧))) ≈˘⟨ homo5 ⟩
  ⟦ ys ++ [ p ] ++ zs ++ [ q ] ++ ws ⟧
    ≈⟨ cong-vec (changeVecView2ʳ i<j q (changeVecView2ˡ i<j p vec≡xs)) ⟩
  ⟦ xs [ i ]≔ p [ j ]≔ q ⟧ ∎ where

  lXsI : lookup xs i ≈₁ x
  lXsI = lookupVecView2ˡ i<j vec≡xs

  lXsJ : lookup xs j ≈₁ w
  lXsJ = lookupVecView2ʳ i<j vec≡xs

  xw≡pq = begin
    ⦅ x ⦆ ∙ ⦅ w ⦆ ≈˘⟨ ∙-cong (cong-⦅⦆ lXsI) (cong-⦅⦆ lXsJ) ⟩
    ⦅ lookup xs i ⦆ ∙ ⦅ lookup xs j ⦆ ≈⟨ eqn ⟩
    ⦅ p ⦆ ∙ ⦅ q ⦆ ∎

swapSameVecI>j : ∀ {xs : Vec A (2 + n)} {i j p q}
  → i > j
  → ⦅ lookup xs i ⦆ ∙ ⦅ lookup xs j ⦆ ≈₂ ⦅ p ⦆ ∙ ⦅ q ⦆
  → ⟦ xs ⟧ ≈₂ ⟦ xs [ i ]≔ p [ j ]≔ q ⟧
swapSameVecI>j {xs = xs} {i} {j} {p} {q} i>j eqn with vec→VecView2 xs i>j
... | view2 {ys = ys} {x} {zs} {w} {ws} vec≡xs = begin
  ⟦ xs ⟧ ≈˘⟨ cong-vec vec≡xs ⟩
  ⟦ ys ++ [ x ] ++ zs ++ [ w ] ++ ws ⟧ ≈⟨ homo5 ⟩
  ⟦ ys ⟧ ∙ (⦅ x ⦆ ∙ (⟦ zs ⟧ ∙ (⦅ w ⦆ ∙ ⟦ ws ⟧))) ≈⟨ swap5' ⟩
  ⦅ w ⦆ ∙ ⦅ x ⦆ ∙ (⟦ ys ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ ws ⟧)) ≈⟨ ∙-congʳ xw≡pq ⟩
  ⦅ p ⦆ ∙ ⦅ q ⦆ ∙ (⟦ ys ⟧ ∙ (⟦ zs ⟧ ∙ ⟦ ws ⟧)) ≈˘⟨ swap5' ⟩
  ⟦ ys ⟧ ∙ (⦅ q ⦆ ∙ (⟦ zs ⟧ ∙ (⦅ p ⦆ ∙ ⟦ ws ⟧))) ≈˘⟨ homo5 ⟩
  ⟦ ys ++ [ q ] ++ zs ++ [ p ] ++ ws ⟧
    ≈⟨ cong-vec (changeVecView2ˡ i>j q (changeVecView2ʳ i>j p vec≡xs)) ⟩
  ⟦ xs [ i ]≔ p [ j ]≔ q ⟧ ∎ where

  lXsI : lookup xs i ≈₁ w
  lXsI = lookupVecView2ʳ i>j vec≡xs

  lXsJ : lookup xs j ≈₁ x
  lXsJ = lookupVecView2ˡ i>j vec≡xs

  xw≡pq = begin
    ⦅ w ⦆ ∙ ⦅ x ⦆ ≈˘⟨ ∙-cong (cong-⦅⦆ lXsI) (cong-⦅⦆ lXsJ) ⟩
    ⦅ lookup xs i ⦆ ∙ ⦅ lookup xs j ⦆ ≈⟨ eqn ⟩
    ⦅ p ⦆ ∙ ⦅ q ⦆ ∎


swapSameVecLookup : ∀ {xs : Vec A n} {i j p q}
  → i ≢ j
  → ⦅ lookup xs i ⦆ ∙ ⦅ lookup xs j ⦆ ≈₂ ⦅ p ⦆ ∙ ⦅ q ⦆
  → ⟦ xs ⟧ ≈₂ ⟦ xs [ i ]≔ p [ j ]≔ q ⟧
swapSameVecLookup {n = ℕ.suc ℕ.zero} {xs} {zero} {zero} i≢j eqn = ⊥-elim (i≢j ≡.refl)
swapSameVecLookup {n = ℕ.suc (ℕ.suc n)} {xs = xs} {i} {j} i≢j eqn with <-cmp i j
... | tri≈ _ i≡j _ = ⊥-elim (i≢j i≡j)
... | tri< i<j _ _ = swapSameVecI<j i<j eqn
... | tri> _ _ i>j = swapSameVecI>j i>j eqn
