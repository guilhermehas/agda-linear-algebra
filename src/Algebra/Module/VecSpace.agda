open import Level using (Level; _⊔_)
open import Function
open import Algebra
open import Algebra.Module
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Maybe using (Maybe; map)
open import Data.Product
open import Data.Sum renaming ([_,_] to [_⊕_])
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Nat.Properties as ℕ hiding (_≟_)
open import Data.Vec as V renaming (_∷_ to _::_) using (Vec; [])
open import Data.Fin hiding (_+_; _-_)
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Data.Fin.Permutation as ↭ hiding (remove; _≈_)
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
import Algebra.Solver.CommutativeMonoid as CMonoidSolver

open import Vector.Base
import Vector.Setoid.Properties as VecProps
open import Vector.Properties
open import Vector.Permutation
import Algebra.Module.Base as MBase
import Algebra.Module.Definition as MDefinitions
import Algebra.Module.DefsField as DField
open import Algebra.BigOps

open import Vec.Updates.Base renaming (_∷_ to _::_)
open import Vec.Relation.FirstOrNot

module Algebra.Module.VecSpace {rr ℓr mr ℓm}
  {ring : Ring rr ℓr}
  (leftModule : LeftModule ring mr ℓm)
  where

infixl 4 _≈ⱽ_

open MBase ring
open module R = Ring ring renaming (Carrier to R)
open LeftModule leftModule renaming (Carrierᴹ to M)
open ≋-props ≈ᴹ-setoid
open SetoidProps ≈ᴹ-setoid
open VecProps ≈ᴹ-setoid
module ≈ᴹ-Reasoning = ≈-Reasoning ≈ᴹ-setoid
module ≈ᴹ = Setoid ≈ᴹ-setoid
module ≋-Reasoning {n} = ≈-Reasoning (≋-setoid n)
open MDefinitions leftModule
open SumCommMonoid +ᴹ-commutativeMonoid

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

matOps→func : VecOp n → Vector M n → Vector M n
matOps→func (swapOp p q p≢q)    xs = swapV xs p q
matOps→func (addCons p q p≢q r) xs = xs [ q ]← r *[ p ]

matOps→func-cong : (xs ys : Vector M n) (mOps : VecOp n) → xs ≋ ys → matOps→func mOps xs ≋ matOps→func mOps ys
matOps→func-cong xs ys (swapOp p q p≢q) xs≈ys i = []≔-cong (xs≈ys _) ([]≔-cong (xs≈ys _) xs≈ys _) q i
matOps→func-cong xs ys (addCons p q p≢q r) xs≈ys i with does $ q ≟ i
... | false = xs≈ys i
... | true  = +ᴹ-cong (xs≈ys i) (*ₗ-cong R.refl (xs≈ys p))

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

open _reaches_ renaming (ys to ws; xs*ys≈x to xs*ws≈x)
open _≋ⱽ_
open CMonoidSolver +ᴹ-commutativeMonoid hiding (_≟_)


≈ⱽ⇒⊆ⱽ : xs ≈ⱽ ys → xs ⊆ⱽ ys
ws (≈ⱽ⇒⊆ⱽ (idR x) record { ys = ys ; xs*ys≈x = xs*ys≈x }) = ys
xs*ws≈x (≈ⱽ⇒⊆ⱽ (idR {xs = xs} {ys = zs} xs≈zs) {x} record { ys = ys ; xs*ys≈x = xs*zs≈x }) = begin
  ∑ (ys *ᵣ zs) ≈˘⟨ ∑Ext (*ₗ-congˡ ∘ xs≈zs) ⟩
  ∑ (ys *ᵣ xs) ≈⟨ xs*zs≈x ⟩
  x ∎ where open ≈ᴹ-Reasoning
ws (≈ⱽ⇒⊆ⱽ (rec (swapOp p q p≢q) xs≈ⱽys swap≈ys) {x} reach@record { ys = ys ; xs*ys≈x = xs*ys≈x }) = swapV (≈ⱽ⇒⊆ⱽ xs≈ⱽys reach .ws) p q
xs*ws≈x (≈ⱽ⇒⊆ⱽ {n} {ys = yss} (rec {xs = xs} {zs} (swapOp p q p≢q) xs≈ⱽys swap≈ys) {x} reach@record { ys = ys ; xs*ys≈x = xs*ys≈x }) = begin
  ∑ (sws *ᵣ yss) ≈˘⟨ ∑Ext (*ₗ-congˡ ∘ swap≈ys) ⟩
  ∑ (sws *ᵣ swapV zs p q) ≈⟨ ∑Ext {n} sameness ⟩
  ∑ (swapV (wss *ᵣ zs) p q) ≈⟨ ∑Swap (wss *ᵣ zs) p q ⟩
  ∑ (wss *ᵣ zs) ≈⟨ help .xs*ws≈x ⟩
  x ∎ where
  open ≈ᴹ-Reasoning

  eqn = ≈ⱽ⇒⊆ⱽ xs≈ⱽys
  help = eqn reach
  wss = ws help
  sws = swapV wss p q
  wssZs = wss *ᵣ zs


  sameness : sws *ᵣ swapV zs p q ≋ swapV (wss *ᵣ zs) p q
  sameness k = begin
    swapV wss p q k *ₗ swapV zs p q k ≈⟨ *ₗ-congʳ (reflexive
      (vecUpdates≡reflectBool-theo2 wss indices valuesWss k)) ⟩
    evalFromPosition valuesWss (wss k) evaluatedWss *ₗ swapV zs p q k ≈⟨ *ₗ-congˡ
      (≈ᴹ-reflexive (vecUpdates≡reflectBool-theo2 zs indices val2 k)) ⟩
    _ *ₗ _ ≈⟨ helper _ (vBoolFromIndices indices k .proj₂) ⟩
    _ ≈˘⟨ ≈ᴹ-reflexive (vecUpdates≡reflectBool-theo2 wssZs indices val3 k) ⟩
    swapV wssZs p q k ∎
    where

    indices = q :: p :: V.[]
    valuesWss = wss p :: wss q :: V.[]
    evaluatedWss = firstTrue $ proj₁ $ vBoolFromIndices indices k

    val2 = zs p :: zs q :: V.[]
    val3 = wssZs p :: wssZs q :: V.[]

    helper : ∀ vBool (vType : VecWithType (λ (ind , b) → Reflects (k ≡ ind) b) $ V.zip indices vBool) →
      evalFromPosition valuesWss (wss k) (firstTrue vBool) *ₗ evalFromPosition val2 (zs k) (firstTrue vBool) ≈ᴹ
      evalFromPosition val3 (wssZs k) (firstTrue vBool)
    helper (true :: _) (ofʸ ≡.refl :: _) = ≈ᴹ-refl
    helper (false :: true :: V.[]) (ofⁿ _ :: ofʸ ≡.refl :: []) = ≈ᴹ-refl
    helper (false :: false :: V.[]) (ofⁿ _ :: ofⁿ _ :: []) = ≈ᴹ-refl
ws (≈ⱽ⇒⊆ⱽ {ys = yss} (rec {xs = xs} {zs} (addCons p q p≢q r) xs≈ⱽys zs≋ys) x∈xs) =
  let wss = ws (≈ⱽ⇒⊆ⱽ xs≈ⱽys x∈xs) in wss [ p ]≔ (wss p - wss q * r)
xs*ws≈x (≈ⱽ⇒⊆ⱽ {n} {ys = yss} (rec {xs = xs} {zs} (addCons p q p≢q r) xs≈ⱽys zs≋ys) {x} x∈xs) = begin
  ∑ (sws *ᵣ yss) ≈˘⟨ ∑Ext (*ₗ-congˡ ∘ zs≋ys) ⟩
  ∑ (sws *ᵣ (zs [ q ]← r *[ p ])) ≈⟨ sameness ⟩
  ∑ (wss *ᵣ zs) ≈⟨ help .xs*ws≈x ⟩
  x ∎
  where
  open ≈ᴹ-Reasoning
  module ∼ = ≈-Reasoning R.setoid

  help = ≈ⱽ⇒⊆ⱽ xs≈ⱽys x∈xs
  wss = ws help
  sws : Vector R n
  sws = wss [ p ]≔ (wss p - wss q * r)

  q≢p = p≢q ∘ ≡.sym

  wss*zs = wss *ᵣ zs
  sws*zs = sws *ᵣ (zs [ q ]← r *[ p ])

  zsPq≡ : (zs [ q ]← r *[ p ]) q ≡ zs q +ᴹ r *ₗ zs p
  zsPq≡ rewrite dec-yes (q ≟ q) ≡.refl .proj₂ = ≡.refl

  sws*zsP≡ : sws*zs p ≡ sws p *ₗ zs p
  sws*zsP≡ rewrite dec-no (q ≟ p) (p≢q ∘ ≡.sym) = ≡.refl

  sws*zsK≡ : ∀ {k} → k ≢ q → sws*zs k ≡ sws k *ₗ zs k
  sws*zsK≡ {k} k≢q rewrite dec-no (q ≟ k) (k≢q ∘ ≡.sym) = ≡.refl

  sws*zsQ : sws*zs q ≈ᴹ sws q *ₗ zs q +ᴹ (sws q * r) *ₗ zs p
  sws*zsQ = begin
    _ ≈⟨ *ₗ-congˡ (≈ᴹ-reflexive zsPq≡) ⟩
    sws q *ₗ (zs q +ᴹ r *ₗ zs p) ≈⟨ *ₗ-distribˡ _ _ _ ⟩
    sws q *ₗ zs q +ᴹ sws q *ₗ r *ₗ zs p ≈˘⟨ +ᴹ-congˡ (*ₗ-assoc _ _ _) ⟩
    _ ∎

  swsP : sws p + sws q * r ≈ wss p
  swsP = ∼.begin
    sws p + sws q * r ∼.≈⟨ +-cong (reflexive (updateAt-updates p wss))
      (*-congʳ (reflexive (updateAt-minimal q p _ q≢p))) ⟩
    wss p - wss q * r + wss q * r ∼.≈⟨ R.+-assoc (wss p) _ _ ⟩
    wss p + (- (wss q * r) + wss q * r) ∼.≈⟨ +-congˡ (-‿inverseˡ _) ⟩
    wss p + 0# ∼.≈⟨ R.+-identityʳ _ ⟩
    wss p ∼.∎

  swsQ : sws q ≈ wss q
  swsQ = reflexive (updateAt-minimal q p wss q≢p)

  lemma₁ : (sws p + sws q * r) *ₗ zs p +ᴹ sws q *ₗ zs q ≈ᴹ wss p *ₗ zs p +ᴹ wss q *ₗ zs q
  lemma₁ = +ᴹ-cong (*ₗ-congʳ swsP) (*ₗ-congʳ swsQ)

  theo₀ : sws*zs p +ᴹ sws*zs q ≈ᴹ wss*zs p +ᴹ wss*zs q
  theo₀ = begin
    _ ≈⟨ +ᴹ-cong (≈ᴹ-reflexive sws*zsP≡) sws*zsQ ⟩
    sws p *ₗ zs p +ᴹ (sws q *ₗ zs q +ᴹ (sws q * r) *ₗ zs p) ≈⟨
      solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ (a ⊕ c) ⊕ b) ≈ᴹ-refl (sws p *ₗ zs p) (sws q *ₗ zs q) ((sws q * r) *ₗ zs p) ⟩
    sws p *ₗ zs p +ᴹ (sws q * r) *ₗ zs p +ᴹ sws q *ₗ zs q ≈˘⟨ +ᴹ-congʳ (*ₗ-distribʳ (zs p) _ _) ⟩
    (sws p + sws q * r) *ₗ zs p +ᴹ sws q *ₗ zs q ≈⟨ lemma₁ ⟩
    _ ∎

  theo₁ : sws*zs p +ᴹ (sws*zs [ p ]≔ 0ᴹ) q ≈ᴹ wss*zs p +ᴹ (wss*zs [ p ]≔ 0ᴹ) q
  theo₁ = begin
    _ +ᴹ _ ≈⟨ +ᴹ-congˡ (≈ᴹ-reflexive (updateAt-minimal q p sws*zs q≢p)) ⟩
    _ +ᴹ sws*zs q ≈⟨ theo₀ ⟩
    _ +ᴹ wss*zs q ≈˘⟨ +ᴹ-congˡ (≈ᴹ-reflexive (updateAt-minimal q p wss*zs q≢p)) ⟩
    _ +ᴹ _ ∎

  theo₂ : sws*zs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ ≋ wss*zs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ
  theo₂ k = helper _ $ vBoolFromIndices indices k .proj₂
    where
    indices = q :: p :: V.[]
    v0 = 0ᴹ :: 0ᴹ :: V.[]


    helper : ∀ vBool (vType : VecIndBool indices vBool k)
      → (sws*zs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) k ≈ᴹ (wss*zs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) k
    helper (true :: _) vt@(ofʸ ≡.refl :: _) = begin
      _   ≡⟨ vecUpdates≡reflectBool-theo sws*zs v0 k vt ⟩
      0ᴹ ≡˘⟨ vecUpdates≡reflectBool-theo wss*zs v0 k vt ⟩
      _ ∎
    helper (false :: true :: _) vt@(_ :: _ :: _) = ≈ᴹ-reflexive (≡.trans
      (vecUpdates≡reflectBool-theo sws*zs v0 k vt) (≡.sym $ vecUpdates≡reflectBool-theo wss*zs v0 k vt))
    helper (false :: false :: V.[]) vt@(ofⁿ k≢q :: ofⁿ k≢p :: []) = begin
      _              ≡⟨ vecUpdates≡reflectBool-theo sws*zs v0 k vt ⟩
      sws*zs k       ≡⟨ sws*zsK≡ k≢q ⟩
      _ *ₗ zs k      ≈⟨ *ₗ-congʳ (reflexive (updateAt-minimal k p _ k≢p)) ⟩
      wss k *ₗ zs k ≡˘⟨ vecUpdates≡reflectBool-theo wss*zs v0 k vt ⟩
      _ ∎


  sameness : ∑ (sws *ᵣ (zs [ q ]← r *[ p ])) ≈ᴹ ∑ (wss *ᵣ zs)
  sameness = begin
    ∑ sws*zs ≈⟨ ∑Remove₂ sws*zs p ⟩
    sws*zs p +ᴹ _ ≈⟨ +ᴹ-congˡ (∑Remove₂ {n} _ q) ⟩
    sws*zs p +ᴹ (_ +ᴹ _) ≈˘⟨ +ᴹ-assoc (sws*zs p) _ _ ⟩
    sws*zs p +ᴹ (sws*zs [ p ]≔ 0ᴹ) q +ᴹ _ ≈⟨ +ᴹ-cong theo₁ (∑Ext theo₂) ⟩
    wss*zs p +ᴹ (wss*zs [ p ]≔ 0ᴹ) q  +ᴹ _ ≈⟨ +ᴹ-assoc _ _ _ ⟩
    wss*zs p +ᴹ (_ +ᴹ _) ≈˘⟨ +ᴹ-congˡ (∑Remove₂ {n} _ q) ⟩
    wss*zs p +ᴹ _ ≈˘⟨ ∑Remove₂ wss*zs p ⟩
    ∑ wss*zs ∎

≈ⱽ-sym : Symmetric (_≈ⱽ_ {n = n})
≈ⱽ-sym (idR xs≈ys) = idR (≋-sym xs≈ys)
≈ⱽ-sym {x = xs} {zs} (rec {ys = ys} (MBase.swapOp p q p≢q) xs≈ⱽys fMops) =
  ≈ⱽ-trans (rec (swapOp p q p≢q) (idR (≋-sym fMops)) λ i → ≈ᴹ-reflexive (swap-involute ys p q i)) ys≈ⱽxs
  where
  ys≈ⱽxs = ≈ⱽ-sym xs≈ⱽys
≈ⱽ-sym {x = xs} {zs} (rec {ys = ys} (MBase.addCons p q p≢q r) xs≈ⱽys fMops) =
  ≈ⱽ-trans (rec (addCons p q p≢q (- r)) (idR (≋-sym fMops)) sameVec) ys≈ⱽxs
  where
  ys≈ⱽxs = ≈ⱽ-sym xs≈ⱽys

  sameVec : ((ys [ q ]← r *[ p ]) [ q ]← - r *[ p ]) ≋ ys
  sameVec i with q ≟ i
  ... | no q≢i rewrite dec-no (q ≟ i) q≢i | dec-no (q ≟ i) q≢i = ≈ᴹ-refl
  ... | yes ≡.refl rewrite dec-yes (i ≟ i) ≡.refl .proj₂ | dec-no (i ≟ p) (p≢q ∘ ≡.sym) = begin
    ys i +ᴹ r *ₗ ys p +ᴹ - r *ₗ ys p ≈⟨ +ᴹ-assoc _ _ _ ⟩
    ys i +ᴹ (r *ₗ ys p +ᴹ - r *ₗ ys p) ≈⟨ +ᴹ-congˡ (begin
       _ ≈˘⟨ *ₗ-distribʳ (ys p) r (- r) ⟩
       (r - r) *ₗ ys p ≈⟨ *ₗ-congʳ (-‿inverseʳ _) ⟩
       0# *ₗ ys p ≈⟨ *ₗ-zeroˡ _ ⟩
       _ ∎
       ) ⟩
    ys i +ᴹ 0ᴹ ≈⟨ +ᴹ-identityʳ _ ⟩
    ys i ∎
    where open ≈ᴹ-Reasoning

≈ⱽ⇒⊇ⱽ : xs ≈ⱽ ys → xs ⊇ⱽ ys
≈ⱽ⇒⊇ⱽ = ≈ⱽ⇒⊆ⱽ ∘ ≈ⱽ-sym

≈ⱽ⇒≋ⱽ : xs ≈ⱽ ys → xs ≋ⱽ ys
≈ⱽ⇒≋ⱽ xs≈ⱽys = record { fwd = ≈ⱽ⇒⊆ⱽ xs≈ⱽys ; bwd = ≈ⱽ⇒⊇ⱽ xs≈ⱽys }
