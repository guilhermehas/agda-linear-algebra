{-# OPTIONS --allow-unsolved-metas #-}

open import Level using (Level; _⊔_)
open import Function
open import Algebra
open import Algebra.Module
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum renaming ([_,_] to [_⊕_])
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Nat.Properties as ℕ hiding (_≟_)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Data.Fin.Permutation as ↭ hiding (remove)
open import Data.Fin.Permutation.Components renaming (transpose to transposeC)
open import Data.List as L using (List)
open import Data.Vec.Functional hiding (transpose)
open import Data.Vec.Functional.Properties hiding (++-cong)
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as ≋-props
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality as ≡ hiding (sym)
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Vector.Base
import Vector.Setoid.Properties as VecProps
open import Vector.Properties
open import Vector.Permutation

module Algebra.Module.VecSpace {rr ℓr mr ℓm}
  {ring : Ring rr ℓr}
  (leftModule : LeftModule ring mr ℓm)
  where

infixl 4 _≈ⱽ_

open Ring ring renaming (Carrier to R)
open LeftModule leftModule renaming (Carrierᴹ to M)
open ≋-props ≈ᴹ-setoid
open SetoidProps ≈ᴹ-setoid
open VecProps ≈ᴹ-setoid
module ≈ᴹ-Reasoning = ≈-Reasoning ≈ᴹ-setoid
module ≈ᴹ = Setoid ≈ᴹ-setoid
module ≋-Reasoning {n} = ≈-Reasoning (≋-setoid n)

private variable
  m n : ℕ
  x y : M
  i j p q : Fin n
  xs xs‵ ys ys‵ zs : Vector M n
  r : R

_[_]←_*[_] : Vector M n → Fin n → R → Fin n → Vector M n
(M [ q ]← r *[ p ]) i with does (q ≟ i)
... | true = M i +ᴹ r *ₗ M p
... | false = M i

data VecOp (n : ℕ) : Set rr where
  swapOp  : (p q : Fin n) (p≢q : p ≢ q)         → VecOp n
  addCons : (p q : Fin n) (p≢q : p ≢ q) (r : R) → VecOp n

matOps→func : VecOp n → Vector M n → Vector M n
matOps→func (swapOp p q p≢q)    xs = swapV xs p q
matOps→func (addCons p q p≢q r) xs = xs [ q ]← r *[ p ]

matOps→func-cong : (xs ys : Vector M n) (mOps : VecOp n) → xs ≋ ys → matOps→func mOps xs ≋ matOps→func mOps ys
matOps→func-cong xs ys (swapOp p q p≢q) xs≈ys i = {!!}
matOps→func-cong xs ys (addCons p q p≢q r) xs≈ys i = {!!}

private
  opposite-injective : Injective _≡_ _≡_ (opposite {n})
  opposite-injective {ℕ.suc n} {i} {j} eq = toℕ-injective $ ∸-cancelˡ-≡ {m = n} (toℕ≤pred[n] i) (toℕ≤pred[n] j) (begin
    n ∸ toℕ i       ≡˘⟨ opposite-prop i ⟩
    toℕ (opposite i) ≡⟨ cong toℕ eq ⟩
    toℕ (opposite j) ≡⟨ opposite-prop j ⟩
    n ∸ toℕ j ∎)
    where open ≡-Reasoning


opVecOps : Op₁ $ VecOp n
opVecOps (swapOp p q p≢q) = swapOp (opposite p) (opposite q) $ p≢q ∘ opposite-injective
opVecOps (addCons p q p≢q r) = addCons (opposite p) (opposite q) (p≢q ∘ opposite-injective) r

invVecOp : Op₁ $ VecOp n
invVecOp (swapOp p q p≢q) = swapOp q p (p≢q ∘ ≡.sym)
invVecOp (addCons p q p≢q r) = addCons q p (p≢q ∘ ≡.sym) r

involute-inv : (xs : Vector M n) (mOps : VecOp n)
  → matOps→func (invVecOp mOps) (matOps→func mOps xs) ≋ xs
involute-inv xs (swapOp p q p≢q) i = begin
  swapV (swapV xs p q) q p i ≡⟨ swap-exchange (swapV xs p q) _ _ i ⟩
  swapV (swapV xs p q) p q i ≡⟨ swap-involute xs _ _ _ ⟩
  xs i ∎
  where open ≈ᴹ-Reasoning
involute-inv xs (addCons p q p≢q r) i = {!!}

data _≈ⱽ_ : Rel (Vector M n) (rr ⊔ mr ⊔ ℓm) where
  idR : xs ≋ ys → xs ≈ⱽ ys
  rec : (mOps : VecOp n)
    → xs ≈ⱽ ys
    → matOps→func mOps ys ≋ zs
    → xs ≈ⱽ zs

≈ⱽ⇒listVops : {xs : Vector M n} → xs ≈ⱽ ys → List (VecOp n)
≈ⱽ⇒listVops (idR _) = L.[]
≈ⱽ⇒listVops (rec mOps xs≈ⱽys _) = mOps L.∷ ≈ⱽ⇒listVops xs≈ⱽys

∷≈≋→≈ⱽ : x ≈ᴹ y → xs ≋ ys → (x ∷ xs) ≈ⱽ (y ∷ ys)
∷≈≋→≈ⱽ = idR ∘₂ ≋-cons

[]←suc : ∀ x xs r (p q : Fin n)
  → ((x ∷ xs) [ suc q ]← r *[ suc p ]) ≋ (x ∷ xs [ q ]← r *[ p ])
[]←suc x xs r p q zero    = ≈ᴹ-refl
[]←suc x xs r p q (suc i) with q ≟ i
... | yes _ = ≈ᴹ-refl
... | no  _ = ≈ᴹ-refl

≡r*[] : ∀ (xs : Vector M n) r p q →
  (xs [ q ]← r *[ p ]) q ≡ xs q +ᴹ r *ₗ xs p
≡r*[] xs r p q with q ≟ q
... | yes _ = ≡.refl
... | no ¬q = ⊥-elim (¬q ≡.refl)

≢r*[] : ∀ (xs : Vector M n) r p q {i} → q ≢ i →
  (xs [ q ]← r *[ p ]) i ≡ xs i
≢r*[] xs r p q {i} q≢i with q ≟ i
... | yes q≡i = ⊥-elim (q≢i q≡i)
... | no    _ = ≡.refl

[]←++ : ∀ (xs : Vector M m) (ys : Vector M n) r p q
  → ((xs ++ ys) [ q ↑ˡ n ]← r *[ p ↑ˡ n ])
      ≋ (xs [ q ]← r *[ p ] ++ ys)
[]←++ {m = m} {n = n} xs ys r p q i with q ↑ˡ n ≟ i | toℕ i ℕ.<? m
... | no q↑n≢i | yes i<m = α where
  α : _
  α with q ≟ fromℕ< i<m
  ... | yes refl = ⊥-elim (q↑n≢i (toℕ-injective (begin
    toℕ (fromℕ< i<m ↑ˡ n) ≡⟨ toℕ-↑ˡ _ _ ⟩
    toℕ (fromℕ< i<m)      ≡⟨ toℕ-fromℕ< _ ⟩
    toℕ i ∎))) where open ≡-Reasoning
  ... | no   q≢i = begin
   [ xs ⊕ ys ] (splitAt m i)         ≡⟨ lookup-++-< xs ys i i<m  ⟩
   xs (fromℕ< i<m)                   ≡˘⟨ ≢r*[] xs r p q q≢i ⟩
   (xs [ q ]← r *[ p ]) (fromℕ< i<m) ≡˘⟨ lookup-++-< (xs [ q ]← r *[ p ]) ys i i<m ⟩
   (xs [ q ]← r *[ p ] ++ ys) i ∎ where open ≈ᴹ-Reasoning
... | yes q↑n≡i | no ¬i<m = ⊥-elim (¬i<m (begin-strict
  toℕ i       ≡˘⟨ cong toℕ q↑n≡i ⟩
  toℕ (q ↑ˡ n) ≡⟨ toℕ-↑ˡ _ _ ⟩
  toℕ q        <⟨ toℕ<n _ ⟩
  m ∎)) where open ≤-Reasoning
... | no  _ | no ¬i<m rewrite splitAt-≥ m i (≮⇒≥ ¬i<m) = ≈ᴹ-refl
... | yes refl | yes i<m rewrite splitAt-< m i i<m with q ≟ fromℕ< i<m
...    | yes _ rewrite splitAt-< m (p ↑ˡ n)
  (≤-<-trans (ℕ.≤-reflexive (toℕ-↑ˡ _ _)) (toℕ<n _)) = +ᴹ-congˡ
    (*ₗ-congˡ (≈ᴹ-reflexive (cong xs (toℕ-injective α)))) where
    open ≡-Reasoning
    α = begin
      toℕ (fromℕ< (≤-<-trans (ℕ.≤-reflexive (toℕ-↑ˡ p n)) (toℕ<n p))) ≡⟨ toℕ-fromℕ< _ ⟩
      toℕ (p ↑ˡ n) ≡⟨ toℕ-↑ˡ _ _ ⟩
      toℕ p ∎
...    | no  q≠i = ⊥-elim (q≠i (≡.sym (toℕ-injective
  (≡.trans (toℕ-fromℕ< _) (toℕ-↑ˡ _ _)))))

∷≈ⱽ→≈ⱽ : x ≈ᴹ y → xs ≈ⱽ ys → (x ∷ xs) ≈ⱽ (y ∷ ys)
∷≈ⱽ→≈ⱽ x≈y (idR xs≋ys) = ∷≈≋→≈ⱽ x≈y xs≋ys
∷≈ⱽ→≈ⱽ x≈y (rec (swapOp p q p≢q) xs≈ys mopsM) =
  rec (swapOp (suc p) (suc q) (p≢q ∘ λ where refl → ≡.refl)) (∷≈ⱽ→≈ⱽ x≈y xs≈ys)
  (≋-trans (≈ᴹ-reflexive ∘ swapCons _ _ _ _) (≋-consˡ mopsM))
∷≈ⱽ→≈ⱽ x≈y (rec (addCons p q p≢q r) xs≈ys mopsM) =
  rec (addCons (suc p) (suc q) (p≢q ∘ λ where refl → ≡.refl) r) (∷≈ⱽ→≈ⱽ x≈y xs≈ys)
  (≋-trans ([]←suc _ _ _ _ _) (≋-consˡ mopsM))

≈ⱽ++ : xs ≈ⱽ xs‵ → ys ≋ ys‵ → (xs ++ ys) ≈ⱽ (xs‵ ++ ys‵)
≈ⱽ++ (idR xs≋xs‵) = idR ∘ ++⁺ _≈ᴹ_ xs≋xs‵
≈ⱽ++ {xs‵ = xs‵} {ys‵ = ys‵} (rec {ys = ys} (swapOp p q p≢q) xs≈xs‵ mOpsZ) ys≋ys‵ =
  rec (swapOp (p ↑ˡ _) (q ↑ˡ _) (p≢q ∘ ↑ˡ-injective _ _ _))
    (≈ⱽ++ xs≈xs‵ ys≋ys‵) (begin
      swapV (ys ++ ys‵) (p ↑ˡ _) (q ↑ˡ _) ≈⟨ (λ i → ≈ᴹ-reflexive (swapV-++ ys ys‵ p q i)) ⟩
      swapV ys p q ++ ys‵ ≈⟨ ++-congʳ _ xs‵ mOpsZ ⟩
      xs‵ ++ ys‵ ∎) where open ≋-Reasoning
≈ⱽ++ {xs‵ = xs‵} {ys‵ = ys‵} (rec {ys = ys} (addCons p q p≢q r) xs≈xs‵ mOpsZ) ys≋ys‵ =
  rec (addCons (p ↑ˡ _) (q ↑ˡ _) (p≢q ∘ ↑ˡ-injective _ _ _) r)
    (≈ⱽ++ xs≈xs‵ ys≋ys‵) (begin
      (ys ++ ys‵) [ q ↑ˡ _ ]← r *[ p ↑ˡ _ ] ≈⟨ []←++ _ _ _ p q ⟩
      ys [ q ]← r *[ p ] ++ ys‵ ≈⟨ ++-congʳ (ys [ q ]← r *[ p ]) xs‵ mOpsZ ⟩
      xs‵ ++ ys‵ ∎) where open ≋-Reasoning

≈ⱽ-refl : Reflexive (_≈ⱽ_ {n = n})
≈ⱽ-refl = idR ≋-refl

≈ⱽ-trans : Transitive (_≈ⱽ_ {n = n})
≈ⱽ-trans (idR xs≋ys) (idR ys≋zs) = idR (≋-trans xs≋ys ys≋zs)
≈ⱽ-trans (rec mOps xs≈ⱽys mOpsXs) (idR ys≋zs) = rec mOps xs≈ⱽys (≋-trans mOpsXs ys≋zs)
≈ⱽ-trans xs≈ⱽys (rec {ys = ws} mOpsYsZs ys≈ⱽzs mOpsYs) = rec mOpsYsZs (≈ⱽ-trans xs≈ⱽys ys≈ⱽzs) mOpsYs

≈ⱽ-sym : Symmetric (_≈ⱽ_ {n = n})
≈ⱽ-sym (idR xs≋ys) = idR (≋-sym xs≋ys)
≈ⱽ-sym (rec {xs = xs} {ys} {zs} mOps xs≈ⱽys mOpsYs) = ≈ⱽ-trans (rec (invVecOp mOps) (idR ≋-refl)
  λ i → begin
    matOps→func (invVecOp mOps) zs i ≈⟨ matOps→func-cong zs _ (invVecOp mOps) (≋-sym mOpsYs) i ⟩
    matOps→func (invVecOp mOps) (matOps→func mOps ys) i ≈⟨ involute-inv ys mOps i ⟩
    ys i ∎)
  (≈ⱽ-sym xs≈ⱽys) where open ≈ᴹ-Reasoning

[_,,_] : M → M → Vector M 2
[ x ,, y ] zero = x
[ x ,, y ] (suc i) = y

private
  v→ij : (v : Fin 2) (i j : Fin n) → Fin n
  v→ij 0F i j = i
  v→ij 1F i j = j

stepVecSpace : ∀ {n} → (let n′ = ℕ.suc (ℕ.suc n)) →
  (xs : Vector M n′) (ys : Vector M 2)
  (i j : Fin n′) (let x = xs i) (let y = xs j)
  → i ≢ j
  → [ x ,, y ] ≈ⱽ ys
  → (let x′ = ys 0F) (let y′ = ys 1F)
  → xs ≈ⱽ xs [ i ]≔ x′ [ j ]≔ y′
stepVecSpace xs ys i j i≢j (idR xsIJ≈ys) = idR xs≈zs
  where
  xs≈zs : xs ≋ (xs [ i ]≔ ys 0F [ j ]≔ ys 1F)
  xs≈zs k with k ≟ j
  ... | yes refl = ≈ᴹ.sym $ begin
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ≡⟨ updateAt-updates j _ ⟩
    ys 1F                           ≈˘⟨ xsIJ≈ys 1F ⟩
    xs k ∎ where open ≈ᴹ-Reasoning
  ... | no k≢j with k ≟ i
  ...    | yes ≡.refl = ≈ᴹ.sym $ begin
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
    (xs [ i ]≔ ys 0F) k              ≡⟨ updateAt-updates i _ ⟩
    ys 0F ≈˘⟨ xsIJ≈ys 0F ⟩
    xs k ∎ where open ≈ᴹ-Reasoning
  ...    | no     k≢i = ≈ᴹ.sym $ begin
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ≡⟨ updateAt-minimal _ _ _ k≢j ⟩
    (xs [ i ]≔ ys 0F) k              ≡⟨ updateAt-minimal _ _ _ k≢i ⟩
    xs k ∎ where open ≈ᴹ-Reasoning
stepVecSpace xs ys i j i≢j (rec {ys = zs} (swapOp p q p≢q) xy≈ⱽys swapZsYs) =
  rec (swapOp i′ j′ (proj₁ (helper p q p≢q swapZsYs))) (stepVecSpace _ _ _ _ i≢j xy≈ⱽys) (proj₂ (helper p q p≢q swapZsYs))
  where
  open ≈ᴹ-Reasoning

  i′ = v→ij p i j
  j′ = v→ij q i j

  helper : (p q : Fin 2) (p≢q : p ≢ q)
    (let i′ = v→ij p i j)
    (let j′ = v→ij q i j)
    (let ws = xs [ i ]≔ zs 0F [ j ]≔ zs 1F)
    → swapV zs p q ≋ ys
    →  i′ ≢ j′ × swapV ws i′ j′ ≋ xs [ i ]≔ ys 0F [ j ]≔ ys 1F
  helper 0F 0F p≢q _ = contradiction ≡.refl p≢q
  helper 1F 1F p≢q _ = contradiction ≡.refl p≢q
  proj₁ (helper 0F 1F p≢q _) = i≢j
  proj₁ (helper 1F 0F p≢q _) = i≢j ∘ ≡.sym
  proj₂ (helper 0F 1F p≢q sZs≋ys) k with k ≟ i | k ≟ j
  ... | yes refl | yes refl = contradiction ≡.refl i≢j
  ... | yes refl | no k≢j = begin
    (_ [ j ]≔ _) k       ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ k ]≔ _) k       ≡⟨ updateAt-updates k _ ⟩
    (_ [ j ]≔ _) j       ≡⟨ updateAt-updates j _ ⟩
    zs 1F                ≈⟨ sZs≋ys 0F ⟩
    ys 0F               ≡˘⟨ updateAt-updates i _ ⟩
    (xs [ i ]≔ ys 0F) k ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
  ... | no k≢i | yes refl = begin
    (_ [ k ]≔ _) k ≡⟨ updateAt-updates k _ ⟩
    (_ [ k ]≔ _) i ≡⟨ updateAt-minimal _ k _ (k≢i ∘ ≡.sym) ⟩
    (_ [ i ]≔ _) i ≡⟨ updateAt-updates i _ ⟩
    zs 0F ≈⟨ sZs≋ys _ ⟩
    ys 1F ≡˘⟨ updateAt-updates k _ ⟩
    (_ [ k ]≔ _) k ∎
  ... | no k≢i | no k≢j = begin
    (_ [ j ]≔ _) k  ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ i ]≔ _) k  ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    (_ [ j ]≔ _) k  ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ i ]≔ _) k  ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    xs k           ≡˘⟨ updateAt-minimal _ i _ k≢i ⟩
    (_ [ i ]≔ _) k ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ j ]≔ _) k ∎
  proj₂ (helper 1F 0F p≢q sZs≋ys) k with k ≟ i | k ≟ j
  ... | yes refl | yes refl = contradiction ≡.refl i≢j
  ... | yes refl | no k≢j = begin
    (_ [ k ]≔ _) k  ≡⟨ updateAt-updates k _ ⟩
    (_ [ j ]≔ _) j  ≡⟨ updateAt-updates j _ ⟩
    zs 1F           ≈⟨ sZs≋ys _ ⟩
    ys 0F          ≡˘⟨ updateAt-updates k _ ⟩
    (_ [ k ]≔ _) k ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ j ]≔ _) k ∎
  ... | no k≢i | yes refl = begin
    (_ [ i ]≔ _) k ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    (_ [ k ]≔ _) k ≡⟨ updateAt-updates k _ ⟩
    (_ [ k ]≔ _) i ≡⟨ updateAt-minimal _ k _ (k≢i ∘ ≡.sym) ⟩
    (_ [ i ]≔ _) i ≡⟨ updateAt-updates i _ ⟩
    zs 0F          ≈⟨ sZs≋ys _ ⟩
    ys 1F         ≡˘⟨ updateAt-updates k _ ⟩
    (_ [ k ]≔ _) k ∎
  ... | no k≢i | no k≢j = begin
    (_ [ i ]≔ _) k  ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    (_ [ j ]≔ _) k  ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ j ]≔ _) k  ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ i ]≔ _) k  ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    xs k           ≡˘⟨ updateAt-minimal _ i _ k≢i ⟩
    (_ [ i ]≔ _) k ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (_ [ j ]≔ _) k ∎

stepVecSpace {n} xs ys i j i≢j (rec {ys = zs} (addCons p q p≢q r) xy≈ⱽys addZsYs) =
  rec (addCons i′ j′ (helper p q p≢q addZsYs .proj₁) r) (stepVecSpace _ _ _ _ i≢j xy≈ⱽys) (helper p q p≢q addZsYs .proj₂)

  where
  open ≈ᴹ-Reasoning

  i′ = v→ij p i j
  j′ = v→ij q i j

  helper : (p q : Fin 2) (p≢q : p ≢ q)
    (let i′ = v→ij p i j)
    (let j′ = v→ij q i j)
    (let ws = xs [ i ]≔ zs 0F [ j ]≔ zs 1F)
    → zs [ q ]← r *[ p ] ≋ ys
    →  i′ ≢ j′ ×  ws [ j′ ]← r *[ i′ ] ≋ xs [ i ]≔ ys 0F [ j ]≔ ys 1F
  helper 0F 0F p≢q = contradiction ≡.refl p≢q
  helper 1F 1F p≢q = contradiction ≡.refl p≢q
  proj₁ (helper 0F 1F p≢q _) = i≢j
  proj₁ (helper 1F 0F p≢q _) = i≢j ∘ ≡.sym
  proj₂ (helper 0F 1F _ zs≋ys) k  with j ≟ k | k ≟ i
  ... | yes refl | yes refl = contradiction ≡.refl i≢j
  ... | yes refl | no k≢i = begin
    (xs [ i ]≔ zs 0F [ k ]≔ zs 1F) k +ᴹ r *ₗ (xs [ i ]≔ zs 0F [ k ]≔ zs 1F) i
      ≈⟨ +ᴹ-cong (≈ᴹ-reflexive (updateAt-updates k _)) (*ₗ-congˡ (≈ᴹ-reflexive
        (≡.trans (updateAt-minimal _ k _ (k≢i ∘ ≡.sym)) (updateAt-updates i xs)))) ⟩
     zs 1F +ᴹ r *ₗ zs 0F            ≈⟨ zs≋ys 1F ⟩
     ys 1F            ≡˘⟨ updateAt-updates k _ ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
  ... | no  j≢k | yes refl = begin
    (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) k ≡⟨ updateAt-minimal _ j _ (j≢k ∘ ≡.sym) ⟩
    (xs [ i ]≔ zs 0F) k              ≡⟨ updateAt-updates k xs ⟩
    zs 0F                            ≈⟨ zs≋ys 0F ⟩
    ys 0F                            ≡˘⟨ updateAt-updates k xs ⟩
    (xs [ i ]≔ ys 0F) k             ≡˘⟨ updateAt-minimal _ j _ (j≢k ∘ ≡.sym) ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
  ... | no j≢k | no k≢i = begin
    (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) k ≡⟨ updateAt-minimal _ j _ (j≢k ∘ ≡.sym) ⟩
    (xs [ i ]≔ zs 0F) k              ≡⟨ updateAt-minimal _ i _ k≢i ⟩
    xs k                            ≡˘⟨ updateAt-minimal _ i _ k≢i ⟩
    (xs [ i ]≔ ys 0F) k             ≡˘⟨ updateAt-minimal _ j _ (j≢k ∘ ≡.sym) ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
  proj₂ (helper 1F 0F p≢q zs≋ys) k with i ≟ k | k ≟ j
  ... | yes refl | yes refl = contradiction ≡.refl i≢j
  ... | yes refl | no k≢j = begin
    (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) i +ᴹ r *ₗ (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) j
      ≈⟨ +ᴹ-cong (≈ᴹ-reflexive (≡.trans (updateAt-minimal _ j _ k≢j) (updateAt-updates i _)))
        (*ₗ-congˡ (≈ᴹ-reflexive (updateAt-updates j _))) ⟩
     zs 0F +ᴹ r *ₗ zs 1F            ≈⟨ zs≋ys 0F ⟩
     ys 0F            ≡˘⟨ updateAt-updates i _ ⟩
     (xs [ i ]≔ ys 0F) i            ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) i ∎
  ... | no i≢k | yes refl = begin
    (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) k ≡⟨ updateAt-updates k _ ⟩
     zs 1F                           ≈⟨ zs≋ys 1F ⟩
     ys 1F                          ≡˘⟨ updateAt-updates k _ ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
  ... | no i≢k | no k≢j = begin
    (xs [ i ]≔ zs 0F [ j ]≔ zs 1F) k ≡⟨ updateAt-minimal _ j _ k≢j ⟩
    (xs [ i ]≔ zs 0F) k              ≡⟨ updateAt-minimal _ i _ (i≢k ∘ ≡.sym) ⟩
    xs k                            ≡˘⟨ updateAt-minimal _ i _ (i≢k ∘ ≡.sym) ⟩
    (xs [ i ]≔ ys 0F) k             ≡˘⟨ updateAt-minimal _ j _ k≢j ⟩
    (xs [ i ]≔ ys 0F [ j ]≔ ys 1F) k ∎
