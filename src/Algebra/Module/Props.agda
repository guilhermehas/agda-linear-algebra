open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module

module Algebra.Module.Props {rr ℓr mr ℓm}
  (cRing : CommutativeRing rr ℓr)
  (open CommutativeRing cRing using (ring))
  (leftModule : LeftModule ring mr ℓm)
  where

open import Level
open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin)
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Binary.Definitions

open import Algebra.Module.Definition leftModule
open import Algebra.BigOps

open CommutativeRing cRing renaming (Carrier to A)
open LeftModule leftModule renaming (Carrierᴹ to M)
open SumCommMonoid +ᴹ-commutativeMonoid
open SumRawRing rawRing using (δ; δss≡δ)

-- open import Algebra.Definitions _≈ᴹ_
open import Algebra.Morphism.Definitions M A _≈_
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid ≈ᴹ-setoid

import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid as ≈ᴹ-Reasoning
import Relation.Binary.Reasoning.Setoid setoid as ≈-Reasoning

private variable
  m n : ℕ
  xs ys zs : Vector M n
  α : A


private module _ where
  open ≈ᴹ-Reasoning

  ∑Mulrdist‵ : (x : A) (V : Vector M n)
            → x *ₗ ∑ V ≈ᴹ ∑ λ i → x *ₗ V i
  ∑Mulrdist‵ {zero} x V = *ₗ-zeroʳ _
  ∑Mulrdist‵ {suc _} x V = begin
    x *ₗ ∑ V                       ≈⟨ *ₗ-distribˡ x (V F.zero) _ ⟩
    x *ₗ V F.zero +ᴹ x *ₗ ∑ (tail V) ≈⟨ +ᴹ-congˡ (∑Mulrdist‵ x (tail V)) ⟩
    x *ₗ V F.zero +ᴹ ∑ (λ i → x *ₗ V (F.suc i)) ∎

  δ*ᵣ-refl : ∀ V (i : Fin n) → ∑ (δ i *ᵣ V) ≈ᴹ V i
  δ*ᵣ-refl {suc n} V F.zero = begin
    1# *ₗ V F.zero +ᴹ ∑ (λ i → δ F.zero (F.suc i) *ₗ tail V i) ≈⟨ +ᴹ-cong (*ₗ-identityˡ _) (begin
      _ ≈⟨ ∑Ext {n} (λ _ → *ₗ-zeroˡ _) ⟩
      ∑ {n} (const 0ᴹ) ≈⟨ ∑0r n ⟩
      0ᴹ ∎
      ) ⟩
    V F.zero +ᴹ 0ᴹ ≈⟨ +ᴹ-identityʳ _ ⟩
    V F.zero ∎
  δ*ᵣ-refl {suc n} V i@(F.suc i′) = begin
    0# *ₗ _ +ᴹ ∑ {n} (λ j → δ i (F.suc j) *ₗ tail V j) ≈⟨ +ᴹ-cong (*ₗ-zeroˡ _) (begin
      _                                ≈⟨ ∑Ext (λ j → *ₗ-congʳ (reflexive (δss≡δ i′ j))) ⟩
      ∑ {n} (λ j → δ i′ j *ₗ tail V j) ≈⟨ δ*ᵣ-refl (tail V) i′ ⟩
      _ ∎
      ) ⟩
    0ᴹ +ᴹ V i  ≈⟨ +ᴹ-identityˡ _ ⟩
    V i ∎


xsReachesItself : ∀ xs (i : Fin n) → xs reaches xs i
xsReachesItself xs i = record { ys = δ i ; xs*ys≈x = δ*ᵣ-refl xs i }

record FunctionAxioms (f : M → A) : Set (mr ⊔ ℓr ⊔ ℓm ⊔ rr) where
  field
    f0 : f 0ᴹ ≈ 0#
    fDist : Homomorphic₂ f _+ᴹ_ _+_
    fCong : Congruent _≈ᴹ_ _≈_ f
    *ₗ-dist : ∀ α x → f (α *ₗ x) ≈ α * f x


sameSolutions : {f : M → A} → FunctionAxioms f → xs ⊆ⱽ ys →
  α isSolutionOf ys by (λ x → f x ≈ 0#) → α isSolutionOf xs by λ x → f x ≈ 0#
sameSolutions {m} {xs} {n} {ys} {α} {f = f} fAxioms xs⊆ys αXs k
  with xs⊆ys (xsReachesItself xs k)
sameSolutions {m} {xs} {ℕ.zero} {ys} {α} {f = f} fAxioms xs⊆ys αXs k
  | record { ys = ws ; xs*ys≈x = xs*ws≈x }
  = begin
    f (α *ₗ xs k) ≈˘⟨ fCong (*ₗ-congˡ xs*ws≈x) ⟩
    f (α *ₗ 0ᴹ)    ≈⟨ fCong (*ₗ-zeroʳ _) ⟩
    f 0ᴹ           ≈⟨ f0 ⟩
    0# ∎
  where
  open ≈-Reasoning
  open FunctionAxioms fAxioms
sameSolutions {m} {xs} {suc n} {ys} {α} {f = f} fAxioms xs⊆ys αXs k
  | record { ys = ws ; xs*ys≈x = xs*ws≈x }
  = begin
  f (α *ₗ xs k) ≈˘⟨ fCong (*ₗ-congˡ xs*ws≈x) ⟩
  f (α *ₗ ∑ (ws *ᵣ ys)) ≈⟨ fCong (∑Mulrdist‵ α (ws *ᵣ ys)) ⟩
  f (α *ₗ (ws 0F *ₗ ys 0F) +ᴹ ∑ λ i → α *ₗ (tail ws i *ₗ tail ys i)) ≈⟨ fDist _ _ ⟩
  f (α *ₗ (ws 0F *ₗ ys 0F)) + f(∑ λ i → α *ₗ (tail ws i *ₗ tail ys i)) ≈⟨ +-cong
    (begin
      _ ≈⟨ {!αXs!} ⟩
      {!!} ≈⟨ {!!} ⟩
      -- {!!} ≈⟨ {!!} ⟩
      {!!} ∎)
    (sameSolutions {!fAxioms!} {!!} {!!} {!!}) ⟩
  {!!} ≈⟨ {!!} ⟩
  -- {!!} ≈⟨ {!!} ⟩
  0# ∎
  where
  open FunctionAxioms fAxioms

  lemma-sum : ∀ i → _
  lemma-sum i = begin
    α *ₗ (ws i *ₗ ys i) ≈˘⟨ *ₗ-assoc α (ws i) (ys i) ⟩
    (α * ws i) *ₗ ys i ≈⟨ *ₗ-congʳ (*-comm _ _) ⟩
    (ws i * α) *ₗ ys i ≈⟨ *ₗ-assoc (ws i) _ _ ⟩
    ws i *ₗ α *ₗ ys i ≈⟨ {!!} ⟩
    -- {!!} ≈⟨ {!!} ⟩
    {!!} ∎
    where
    open ≈ᴹ-Reasoning

  lemma = begin
    α *ₗ xs k ≈˘⟨ *ₗ-congˡ xs*ws≈x ⟩
    α *ₗ ∑ (ws *ᵣ ys) ≈⟨ ∑Mulrdist‵ α (ws *ᵣ ys) ⟩
    (∑ λ i → α *ₗ (ws i *ₗ ys i)) ≈˘⟨ ∑Ext lemma-sum ⟩
    {!!} ≈⟨ {!!} ⟩
    -- {!!} ≈⟨ {!!} ⟩
    {!!} ∎
    where
    open ≈ᴹ-Reasoning


  open ≈-Reasoning

  -- {!begin
  -- α *ₗ xs k ≈˘⟨ *ₗ-congˡ xs*ws≈x ⟩
  -- α *ₗ ∑ (ws *ᵣ ys) ≈⟨ ∑Mulrdist‵ α (ws *ᵣ ys) ⟩
  -- ∑ (λ i → α *ₗ (ws i *ₗ ys i)) ≈⟨ ∑Ext {n} (λ k →  begin
  --   α *ₗ ws k *ₗ ys k  ≈˘⟨ *ₗ-assoc α (ws k) (ys k) ⟩
  --   (α * ws k) *ₗ ys k  ≈⟨ *ₗ-congʳ (*-comm _ _) ⟩
  --   (ws k * α) *ₗ ys k  ≈⟨ *ₗ-assoc (ws k) α (ys k) ⟩
  --   ws k *ₗ α *ₗ ys k   ≈⟨ *ₗ-congˡ {!αXs _) ⟩
  --   ws k *ₗ 0ᴹ          ≈⟨ *ₗ-zeroʳ _ ⟩
  --   0ᴹ ∎) ⟩
  -- ∑ {n} (const 0ᴹ) ≈⟨ ∑0r n ⟩
  -- 0ᴹ ∎!}

open ≈ᴹ-Reasoning

0∷⊆ⱽ : (xs : Vector M n) → (0ᴹ ∷ xs) ⊆ⱽ xs
0∷⊆ⱽ xs {x} (ys by xs*ys≈x) = as by ∑as*xs≈x
  where
  as = tail ys
  ∑as*xs≈x = begin
    ∑ (tail ys *ᵣ xs)           ≈˘⟨ +ᴹ-identityˡ _ ⟩
    0ᴹ +ᴹ _                     ≈˘⟨ +ᴹ-congʳ (*ₗ-zeroʳ _) ⟩
    _ *ₗ 0ᴹ +ᴹ ∑ (tail ys *ᵣ xs) ≈⟨ xs*ys≈x ⟩
    x ∎

⊆ⱽ0∷ : (xs : Vector M n) → xs ⊆ⱽ (0ᴹ ∷ xs)
⊆ⱽ0∷ xs {x} (ys by xs*ys≈x) = as by ∑ws≈x
  where
  as = 0# ∷ ys
  ∑ws≈x = begin
    0# *ₗ 0ᴹ +ᴹ ∑ (ys *ᵣ xs) ≈⟨ +ᴹ-congʳ (*ₗ-zeroˡ _) ⟩
    0ᴹ +ᴹ ∑ (ys *ᵣ xs)       ≈⟨ +ᴹ-identityˡ _ ⟩
    ∑ (ys *ᵣ xs)             ≈⟨ xs*ys≈x ⟩
    x ∎

0∷≈ⱽ : (xs : Vector M n) → (0ᴹ ∷ xs) ≋ⱽ xs
0∷≈ⱽ xs = record { fwd = 0∷⊆ⱽ xs ; bwd = ⊆ⱽ0∷ xs }

≋ⱽ-refl : Reflexive (_≋ⱽ_ {n})
≋ⱽ-refl = record { fwd = id ; bwd = id }

≋ⱽ-sym : Symmetric (_≋ⱽ_ {n})
≋ⱽ-sym record { fwd = fwd ; bwd = bwd } = record { fwd = bwd ; bwd = fwd }

≋ⱽ-trans : xs ≋ⱽ ys → ys ≋ⱽ zs → xs ≋ⱽ zs
≋ⱽ-trans record { fwd = fwdA ; bwd = bwdA } record { fwd = fwdB ; bwd = bwdB } =
  record { fwd = fwdB ∘ fwdA ; bwd = bwdA ∘ bwdB }

≋⇒⊆ⱽ : xs ≋ ys → xs ⊆ⱽ ys
≋⇒⊆ⱽ {n} {xs} {ys} xs≋ys (zs by xs*zs≈x) = zs by ≈ᴹ-trans (∑Ext (*ₗ-congˡ ∘ ≋-sym xs≋ys)) xs*zs≈x

≋⇒≋ⱽ : xs ≋ ys → xs ≋ⱽ ys
≋⇒≋ⱽ xs≋ys = record { fwd = ≋⇒⊆ⱽ xs≋ys ; bwd = ≋⇒⊆ⱽ (≋-sym xs≋ys) }
