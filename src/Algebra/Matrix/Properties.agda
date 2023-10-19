module Algebra.Matrix.Properties where

open import Level using (Level)
open import Function
open import Algebra.Bundles
import Algebra.Definitions as ADefinitions
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.List as L using (List; []; _∷_)
open import Data.Vec.Functional as V
open import Vector.Base as V using (module SetoidProps)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra.Matrix.Structures
open import Algebra.BigOps

private variable
  a ℓ : Level
  l m m₁ m₂ n n₁ n₂ p q k : ℕ
  i j h : Fin n

module MRingProps (ring : Ring a ℓ) where

  open Ring ring hiding (zero)
  open MRing rawRing renaming (Matrix to Matrix′) hiding (flip)
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open SumRing ring
  open IsLinear
  open module AD' {m} {n} = ADefinitions (_≈ᴹ_ {m} {n})
  open module SProps {n} = SetoidProps (≋-setoid n)

  private
    Matrix = Matrix′ Carrier

  private variable
    M N K P Q : Matrix m n
    x y : Vector Carrier n
    r : Carrier

  ≈ᴹ-refl : Reflexive (_≈ᴹ_ {m = m} {n})
  ≈ᴹ-refl i j = refl

  ≈ᴹ-reflexive : (∀ i j → M i j ≡ N i j) → M ≈ᴹ N
  ≈ᴹ-reflexive p i j rewrite p i j = refl

  ≈ᴹ-sym : Symmetric (_≈ᴹ_ {m = m} {n})
  ≈ᴹ-sym M≈N i j = sym (M≈N i j)

  ≈ᴹ-trans : Transitive (_≈ᴹ_ {m = m} {n})
  ≈ᴹ-trans M≈N N≈P i j = trans (M≈N i j) (N≈P i j)

  ≈ᴹ-isEquivalence : IsEquivalence (_≈ᴹ_ {m = m} {n})
  ≈ᴹ-isEquivalence = record
    { refl  = ≈ᴹ-refl
    ; sym   = ≈ᴹ-sym
    ; trans = ≈ᴹ-trans
    }

  ≈ᴹ-setoid : ∀ {m n} → Setoid _ _
  ≈ᴹ-setoid {m} {n} = record
    { isEquivalence = ≈ᴹ-isEquivalence {m} {n}
    }

  module ≈ᴹ-Reasoning {m} {n} = ≈-Reasoning (≈ᴹ-setoid {m} {n})

  *ᴹ-zero : (M : Matrix m n) → 0ᴹ *ᴹ M ≈ᴹ (0ᴹ {m = m})
  *ᴹ-zero {ℕ.zero} M i k = refl
  *ᴹ-zero {ℕ.suc n} M i k = begin
      0# * M zero k + _          ≈⟨ +-congʳ (zeroˡ _) ⟩
      0# + _                     ≈⟨ +-identityˡ _ ⟩
      (∑ λ j → 0# * M (suc j) k) ≈˘⟨ ∑Mulrdist 0# (λ j → M (suc j) k) ⟩
      0# * (∑ λ j → M (suc j) k) ≈⟨ zeroˡ _ ⟩
      0# ∎ where open ≈-Reasoning setoid

  *ᴹ-identityˡ : (M : Matrix m n) → 1ᴹ *ᴹ M ≈ᴹ M
  *ᴹ-identityˡ {ℕ.suc n} M zero k = begin
    (1ᴹ *ᴹ M) zero k  ≡⟨⟩
    (∑ λ j → δ zero j * M j k) ≡⟨⟩
    foldr _+_ 0# {ℕ.suc n} (λ j → δ zero j * M j k) ≡⟨⟩
    δ (zero {n}) zero * M zero k + (∑ λ j → δ zero (suc j) * M (suc j) k) ≡⟨⟩
    1# * M zero k + (∑ λ j → 0# * M (suc j) k) ≈˘⟨ +-congˡ (∑Mulrdist 0# λ j → M (suc j) k) ⟩
    1# * M zero k + 0# * (∑ λ j → M (suc j) k) ≈⟨ +-cong (*-identityˡ _) (zeroˡ _) ⟩
    M zero k + 0# ≈⟨ +-identityʳ _ ⟩
    M zero k ∎ where open ≈-Reasoning setoid
  *ᴹ-identityˡ {ℕ.suc n} M (suc i) k = begin
    (0# * M zero k + _) ≈⟨ +-congʳ (zeroˡ _) ⟩
    (0# + _) ≈⟨ +-identityˡ _ ⟩
    (∑ λ j → δ (suc i) (suc j) * M (suc j) k) ≈⟨ ∑Ext (λ j → *-congʳ (δss≡δ i j))  ⟩
    (∑ λ j → δ i j * M (suc j) k) ≈⟨ *ᴹ-identityˡ (tail M) i k ⟩
    M (suc i) k ∎ where open ≈-Reasoning setoid

  *ᴹ-congˡ : P ≈ᴹ Q → N *ᴹ P ≈ᴹ N *ᴹ Q
  *ᴹ-congˡ P≈Q _ j = ∑Ext λ k → *-congˡ (P≈Q k j)

  ∑Exchange : (M : Matrix m n) → ∑ (λ i → ∑ (λ j → M i j)) ≈ ∑ (λ j → ∑ (λ i → M i j))
  ∑Exchange {ℕ.zero} {n}        M = sym (∑0r n)
  ∑Exchange {ℕ.suc m} {ℕ.zero}  M = begin
    ∑ (λ i → ∑ (M i)) ≈⟨ +-congˡ (∑0r m) ⟩
    0# + 0#           ≈⟨ +-identityˡ 0# ⟩
    0# ∎ where open ≈-Reasoning setoid
  ∑Exchange {ℕ.suc m} {ℕ.suc n} M =
     let a  = M zero zero
         L  = ∑ λ j → M zero (suc j)
         C  = ∑ λ i → M (suc i) zero
         N  = ∑ λ i → ∑ λ j → M (suc i) (suc j)
         -- N reindexed
         N' = ∑ λ j → ∑ λ i → M (suc i) (suc j)
     in begin
     a + L + ∑ (λ i → ∑ (λ j → M (suc i) j)) ≈⟨ +-congˡ (∑Split (λ i → M (suc i) zero) λ i → ∑ (λ j → M (suc i) (suc j))) ⟩
     a + L + (C + N)                         ≈⟨ +-congˡ (+-congˡ (∑Exchange (λ i j → M (suc i) (suc j)))) ⟩
     a + L + (C + N')                        ≈⟨ +-assoc _ _ _ ⟩
     a + (L + (C + N'))                      ≈˘⟨ +-congˡ (+-assoc _ _ _) ⟩
     a + (L + C + N')                        ≈⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
     a + (C + L + N')                        ≈⟨ +-congˡ (+-assoc _ _ _) ⟩
     a + (C + (L + N'))                      ≈˘⟨ +-assoc _ _ _ ⟩
     a + C + (L + N')                        ≈˘⟨ +-congˡ (∑Split (λ j → M zero (suc j)) λ j → ∑ (λ i → M (suc i) (suc j))) ⟩
     a + C + ∑ (λ j → ∑ (λ i → M i (suc j))) ∎
    where open ≈-Reasoning setoid

  *ᴹ-assoc : (M : Matrix m n) (N : Matrix n p) (K : Matrix p q)
    → (M *ᴹ N) *ᴹ K ≈ᴹ M *ᴹ (N *ᴹ K)
  *ᴹ-assoc M N K i j = begin
    ∑ (λ l → ∑ (λ k → M i k * N k l) * K l j)    ≈⟨ ∑Ext (λ l → ∑Mulldist (K l j) (λ k → M i k * N k l)) ⟩
    ∑ (λ l → ∑ (λ k → M i k * N k l * K l j))    ≈⟨ ∑Exchange (λ l k → M i k * N k l * K l j) ⟩
    ∑ (λ k → ∑ (λ l → M i k * N k l * K l j))    ≈⟨ ∑Ext (λ k → ∑Ext (λ l → *-assoc (M i k) (N k l) (K l j))) ⟩
    ∑ (λ k → ∑ (λ l → M i k * (N k l * K l j))) ≈˘⟨ ∑Ext (λ k → ∑Mulrdist (M i k) (λ l → N k l * K l j)) ⟩
    ∑ (λ k → M i k * ∑ (λ l → N k l * K l j)) ∎
    where open ≈-Reasoning setoid

  ++-split : (M : Matrix m₁ n) (N : Matrix m₂ n) (P : Matrix n p) → (M ++ N) *ᴹ P ≈ᴹ M *ᴹ P ++ N *ᴹ P
  ++-split {m₁} M N P i j with splitAt m₁ i
  ... | inj₁ _ = refl
  ... | inj₂ _ = refl

  ++ⱽ-split : (L : Matrix l m) (M : Matrix m n₁) (N : Matrix m n₂) → L *ᴹ (M ++ⱽ N) ≈ᴹ L *ᴹ M ++ⱽ L *ᴹ N
  ++ⱽ-split {n₁ = n₁} L M N i j with splitAt n₁ j
  ... | inj₁ _ = refl
  ... | inj₂ _ = refl

  take-++ : (M : Matrix m₁ n) (N : Matrix m₂ n) → take m₁ (M ++ N) ≈ᴹ M
  take-++ {m₁} {m₂ = m₂} M N i j rewrite splitAt-↑ˡ m₁ i m₂ = refl

  drop-++ : (M : Matrix m₁ n) (N : Matrix m₂ n) → drop m₁ (M ++ N) ≈ᴹ N
  drop-++ {m₁} {m₂ = m₂} M N i j rewrite splitAt-↑ʳ m₁ m₂ i  = refl

  take-++ⱽ : (M : Matrix m n₁) (N : Matrix m n₂) → takeⱽ n₁ (M ++ⱽ N) ≈ᴹ M
  take-++ⱽ {n₁ = n₁} {n₂} M N i j rewrite splitAt-↑ˡ n₁ j n₂ = refl

  drop-++ⱽ : (M : Matrix m n₁) (N : Matrix m n₂) → dropⱽ n₁ (M ++ⱽ N) ≈ᴹ N
  drop-++ⱽ {n₁ = n₁} {n₂} M N i j rewrite splitAt-↑ʳ n₁ n₂ j = refl

  isLinearId : IsLinear {m = m} {n = n} id
  isLinearId .transMat _ = 1ᴹ
  isLinearId .transEq  _ = ≈ᴹ-sym (*ᴹ-identityˡ _)

  module _
    {T₁ : Matrix m n → Matrix k n}
    {T₂ : Matrix k n → Matrix l n}
    (isLinearT₁ : IsLinear T₁)
    (isLinearT₂ : IsLinear T₂) where

    isLinearComp : IsLinear (T₂ ∘ T₁)
    transMat isLinearComp M = isLinearT₂ .transMat (T₁ M) *ᴹ isLinearT₁ .transMat M
    transEq isLinearComp M = begin
      (T₂ ∘ T₁) M
        ≈⟨ isLinearT₂ .transEq _ ⟩
      transMat isLinearT₂ (T₁ M) *ᴹ T₁ M
        ≈⟨ *ᴹ-congˡ {N = transMat isLinearT₂ (T₁ M)} (isLinearT₁ .transEq M) ⟩
      transMat isLinearT₂ (T₁ M) *ᴹ (transMat isLinearT₁ M *ᴹ M)
        ≈˘⟨ *ᴹ-assoc (transMat isLinearT₂ (T₁ M)) (transMat isLinearT₁ M) M ⟩
      transMat isLinearComp M *ᴹ M ∎
      where open ≈ᴹ-Reasoning

  swapIsLinear : (p q : Fin n) → IsLinear {n = m} (swap p q)
  transMat (swapIsLinear p q) _ = swapMatrix p q
  transEq  (swapIsLinear p q) M i j with p ≟ i | q ≟ i
  ... | yes _ | yes _ = sym (∑Mul1r (flip M j) q)
  ... | yes _ | no  _ = sym (∑Mul1r (flip M j) q)
  ... | no  _ | yes _ = sym (∑Mul1r (flip M j) p)
  ... | no  _ | no  _ = sym (∑Mul1r (flip M j) i)

  addConstRowIsLinear : (p q : Fin n) (r : Carrier)
    → IsLinear {n = m} (λ M → M [ p ]≔ r *[ q ])
  transMat (addConstRowIsLinear p q r) _ = addConstRowMatrix p q r
  transEq  (addConstRowIsLinear p q r) M i j with q ≟ i
  ... | yes _ = begin
    M i j + r * M p j ≈˘⟨ +-cong (∑Mul1r (λ k → M k j) _) α ⟩
    ∑ (λ k → δ i k * M k j) + ∑ (λ k → r * δ p k * M k j)  ≈˘⟨ ∑Split _ (λ k → r * δ p k * M k j) ⟩
    ∑ (λ k → δ i k * M k j + r * δ p k * M k j) ≈˘⟨ ∑Ext (λ k → distribʳ (M k j) _ _ ) ⟩
    ∑ (λ k → (δ i k + r * δ p k) * M k j) ∎
    where
      open ≈-Reasoning setoid
      α = begin
        ∑ (λ k → r * δ p k * M k j)   ≈⟨ ∑Ext (λ k → *-assoc _ _ (M k j)) ⟩
        ∑ (λ k → r * (δ p k * M k j)) ≈˘⟨ ∑Mulrdist _ (λ k → δ p k * M k j) ⟩
        r * ∑ (λ k → δ p k * M k j)   ≈⟨ *-congˡ (∑Mul1r (λ k → M k j) _) ⟩
        r * M p j ∎
  ... | no  _ = sym (∑Mul1r (flip M j) i)

  isLinear→bothLinear : {T : Matrix m n → Matrix k n}
    (isLin : IsLinear T) → MatFunAreLinear (transMat isLin) T
  isLinear→bothLinear isLin = record { transEq = transEq isLin }

  bothLinear→isLinear :
    {transMat : (M : Matrix m n) → Matrix k m}
    {T : Matrix m n → Matrix k n} →
    MatFunAreLinear transMat T → IsLinear T
  bothLinear→isLinear {transMat = transMat} bothLin = record
    { transMat = transMat
    ; transEq  = MF.transEq }
    where module MF = MatFunAreLinear bothLin

  matrixOpsLinear : (mops : MatrixOps m n)
    → MatFunAreLinear (const $ matOps→mat mops) (matOps→func mops)
  matrixOpsLinear (swapOp p q)    = isLinear→bothLinear (swapIsLinear p q)
  matrixOpsLinear (addCons p q r) = isLinear→bothLinear (addConstRowIsLinear p q r)

  cong-mopsFunc : ∀ mops → M ≈ᴹ N → matOps→func mops M ≈ᴹ matOps→func mops N
  cong-mopsFunc (swapOp p q) M≈N i j with p ≟ i | q ≟ i
  ... | yes _ | _     = M≈N _ _
  ... | no  _ | yes _ = M≈N _ _
  ... | no  _ | no  _ = M≈N _ _
  cong-mopsFunc (addCons p q r) M≈N i j with q ≟ i
  ... | yes _ = +-cong (M≈N _ _) (*-congˡ (M≈N _ _))
  ... | no  _ = M≈N _ _

  listMatrixOpsLinear : (lMops : List $ MatrixOps m n)
    → MatFunAreLinear (const $ listMatOps→mat lMops) (listMatOps→func lMops)
  listMatrixOpsLinear [] = isLinear→bothLinear isLinearId
  listMatrixOpsLinear (x ∷ lMops) = isLinear→bothLinear
    (isLinearComp (bothLinear→isLinear (listMatrixOpsLinear lMops))
    (bothLinear→isLinear (matrixOpsLinear x)))

  ≈⇒list : ∀ (M≈N : M ≈ᴹ N) list → listMatOps→func list M ≈ᴹ listMatOps→func list N
  ≈⇒list M≈N [] = M≈N
  ≈⇒list M≈N (x ∷ xs) = cong-mopsFunc x (≈⇒list M≈N xs)

  swapII≡const : ∀ p i j → swap p p N i j ≡ N i j
  swapII≡const p i j with p ≟ i
  ... | yes ≡.refl = ≡.refl
  ... | no       _ = ≡.refl

  swapCons : swap i j M ≈ᴹ N → swap (suc i) (suc j) (x V.∷ M) ≈ᴹ x V.∷ N
  swapCons {i = p} {q} swapMN zero j = refl
  swapCons {i = p} {q} swapMN (suc i) j
    with p ≟ i | q ≟ i | swapMN i j
  ... | yes _ |     _ | swapIJ = swapIJ
  ... | no  _ | yes _ | swapIJ = swapIJ
  ... | no  _ | no  _ | swapIJ = swapIJ


  ▹⇒list : (M▹N : M ▹ N) → listMatOps→func (▹⇒listMops M▹N) M ≈ᴹ N
  ▹⇒list (idR M≈N) = M≈N
  ▹⇒list {M = M} {N} (rec {xs = M‵} mOps M▹N mys≈zs) = begin
    matOps→func mOps (listMatOps→func (▹⇒listMops M▹N) M)
      ≈⟨ cong-mopsFunc mOps (▹⇒list M▹N) ⟩
    matOps→func mOps _
    ≈⟨ mys≈zs ⟩
    N ∎
    where open ≈ᴹ-Reasoning

  []▹[] : _▹_ {n = n} V.[] V.[]
  []▹[] = idR (λ ())

  ∷≈▹ : x ≋ y → M ≈ᴹ N → (x V.∷ M) ▹ (y V.∷ N)
  ∷≈▹ = idR ∘₂ ≋-cons

  add∷ : (M [ i ]≔ r *[ j ]) ≈ᴹ N → (x V.∷ M) [ suc i ]≔ r *[ suc j ] ≈ᴹ x V.∷ N
  add∷ Mcons zero j = refl
  add∷ {j = q} Mcons (suc i) j
    with q ≟ i | Mcons i j
  ... | yes _ | consIJ = consIJ
  ... | no  _ | consIJ = consIJ

  ∷▹▹ : x ≋ y → M ▹ N → (x V.∷ M) ▹ (y V.∷ N)
  ∷▹▹ x≋y (idR M≈N) = ∷≈▹ x≋y M≈N
  ∷▹▹ {x = x} {y} {M = M} {N} x≋y (rec (swapOp p q) M▹N mopsM) =
    rec (swapOp (suc p) (suc q))
    (∷▹▹ x≋y M▹N) (swapCons mopsM)
  ∷▹▹ x≋y (rec (addCons p q r) M▹N mopsM) =
    rec (addCons (suc p) (suc q) r) (∷▹▹ x≋y M▹N) (add∷ mopsM)

  ▹▹∷ : ∀ {xs ys : Matrix 1 n} → xs ▹ ys → M ≈ᴹ N → (xs zero V.∷ M) ▹ (ys zero V.∷ N)
  ▹▹∷ (idR x≈y) = ∷≈▹ (x≈y zero)
  ▹▹∷ {N = N} {ys = zs} (rec {ys = ys} (swapOp zero zero) x▹y mYs≈y) M≈N =
    rec (swapOp zero zero)
      (▹▹∷ x▹y M≈N) α
    where
    α : swap zero zero (ys zero V.∷ N) ≈ᴹ zs zero V.∷ N
    α zero = mYs≈y zero
    α (suc i) = ≋-refl
  ▹▹∷ {N = N} {ys = zs} (rec {ys = ys} (addCons zero zero r) x▹y mYs≈y) M≈N =
    rec (addCons zero zero r) (▹▹∷ x▹y M≈N) α
    where

    α : (ys zero V.∷ N) [ zero ]≔ r *[ zero ] ≈ᴹ zs zero V.∷ N
    α zero = mYs≈y zero
    α (suc i) = ≋-refl
