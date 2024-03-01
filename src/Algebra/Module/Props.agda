open import Algebra
open import Algebra.Module

module Algebra.Module.Props {rr ℓr mr ℓm}
  {ring : Ring rr ℓr}
  (leftModule : LeftModule ring mr ℓm)
  where

  open import Function
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Fin as F
  open import Data.Vec.Functional

  open import Algebra.Module.Definition leftModule
  open import Algebra.BigOps

  open Ring ring renaming (Carrier to A)
  open LeftModule leftModule renaming (Carrierᴹ to M)
  open SumMonoid +ᴹ-monoid
  open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

  private variable
    m n : ℕ
    xs ys : Vector M n
    α : A

  private
    ∑Mulrdist‵ : (x : A) (V : Vector M n)
              → x *ₗ ∑ V ≈ᴹ ∑ λ i → x *ₗ V i
    ∑Mulrdist‵ {zero} x V = {!!}
    ∑Mulrdist‵ {suc _} x V = begin
      x *ₗ ∑ V                       ≈⟨ *ₗ-distribˡ x (V F.zero) _ ⟩
      x *ₗ V F.zero +ᴹ x *ₗ ∑ (tail V) ≈⟨ +ᴹ-congˡ (∑Mulrdist‵ x (tail V)) ⟩
      x *ₗ V F.zero +ᴹ ∑ (λ i → x *ₗ V (F.suc i)) ∎

  sameSolutions : xs ⊆ⱽ ys → α isSolutionOf ys → α isSolutionOf xs
  sameSolutions {m} {xs} {n} {ys} {α} xs⊆ys αXs k with xs⊆ys {x = xs k} (record { ys = {!!} ; xs*ys≈x = {!!} })
  ... | record { ys = ws ; xs*ys≈x = xs*ws≈x } = begin
    α *ₗ xs k ≈˘⟨ *ₗ-congˡ xs*ws≈x ⟩
    α *ₗ ∑ (ws *ᵣ ys) ≈⟨ ∑Mulrdist‵ α (ws *ᵣ ys) ⟩
    ∑ (λ i → α *ₗ (ws i *ₗ ys i)) ≈⟨ ∑Ext {n} (λ k →  begin
      α *ₗ ws k *ₗ ys k ≈˘⟨ *ₗ-assoc α (ws k) (ys k) ⟩
      (α * ws k) *ₗ ys k ≈⟨ *ₗ-congʳ {!*-com!} ⟩
      -- maybe needs commutative ring
      {!!} ≈⟨ {!!} ⟩
      0ᴹ ∎) ⟩
    ∑ {n} (const 0ᴹ) ≈⟨ ∑0r n ⟩
    0ᴹ ∎
