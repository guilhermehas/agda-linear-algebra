open import Algebra
open import Algebra.Module

module Algebra.Module.Props {rr ℓr mr ℓm}
  (cRing : CommutativeRing rr ℓr)
  (open CommutativeRing cRing using (ring))
  (leftModule : LeftModule ring mr ℓm)
  where

  open import Function
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin as F using (Fin)
  open import Data.Vec.Functional

  open import Algebra.Module.Definition leftModule
  open import Algebra.BigOps

  open CommutativeRing cRing renaming (Carrier to A)
  open LeftModule leftModule renaming (Carrierᴹ to M)
  open SumCommMonoid +ᴹ-commutativeMonoid
  open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid
  open SumRawRing rawRing using (δ; δss≡δ)

  private variable
    m n : ℕ
    xs ys : Vector M n
    α : A

  private
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

  sameSolutions : xs ⊆ⱽ ys → α isSolutionOf ys → α isSolutionOf xs
  sameSolutions {m} {xs} {n} {ys} {α} xs⊆ys αXs k with xs⊆ys (xsReachesItself xs k)
  ... | record { ys = ws ; xs*ys≈x = xs*ws≈x } = begin
    α *ₗ xs k ≈˘⟨ *ₗ-congˡ xs*ws≈x ⟩
    α *ₗ ∑ (ws *ᵣ ys) ≈⟨ ∑Mulrdist‵ α (ws *ᵣ ys) ⟩
    ∑ (λ i → α *ₗ (ws i *ₗ ys i)) ≈⟨ ∑Ext {n} (λ k →  begin
      α *ₗ ws k *ₗ ys k  ≈˘⟨ *ₗ-assoc α (ws k) (ys k) ⟩
      (α * ws k) *ₗ ys k  ≈⟨ *ₗ-congʳ (*-comm _ _) ⟩
      (ws k * α) *ₗ ys k  ≈⟨ *ₗ-assoc (ws k) α (ys k) ⟩
      ws k *ₗ α *ₗ ys k   ≈⟨ *ₗ-congˡ (αXs _) ⟩
      ws k *ₗ 0ᴹ          ≈⟨ *ₗ-zeroʳ _ ⟩
      0ᴹ ∎) ⟩
    ∑ {n} (const 0ᴹ) ≈⟨ ∑0r n ⟩
    0ᴹ ∎

  open _reaches_ renaming (ys to wws; xs*ys≈x to xs*wws≈x)

  0∷⊆ⱽ : xs ⊆ⱽ ys → (0ᴹ ∷ xs) ⊆ⱽ ys
  0∷⊆ⱽ {n} {xs} {zs} {as} xs⊆ⱽys {x} (ys by xs*ys≈x) = _ by xs*ws≈x where

    ∑tys≈0+∑t = begin
      ∑ (tail ys *ᵣ xs)       ≈˘⟨ +ᴹ-identityˡ _ ⟩
      0ᴹ +ᴹ ∑ (tail ys *ᵣ xs) ≈˘⟨ +ᴹ-congʳ (*ₗ-zeroʳ _) ⟩
      _ *ₗ 0ᴹ +ᴹ ∑ (tail ys *ᵣ xs) ∎

    ∑ws≈∑ys = xs⊆ⱽys (tail ys by ∑tys≈0+∑t)
    xs*ws≈x = begin
      ∑ (_ *ᵣ as) ≈⟨ ∑ws≈∑ys .xs*wws≈x  ⟩
      _ *ₗ 0ᴹ +ᴹ ∑ (tail (ys *ᵣ (0ᴹ ∷ xs))) ≈⟨ xs*ys≈x ⟩
      x ∎
