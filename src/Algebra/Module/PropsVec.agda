open import Algebra

module Algebra.Module.PropsVec
  {rr ℓr}
  (cRing : CommutativeRing rr ℓr)
  where

import Algebra.Module.Props as MProps′
open import Function
open import Algebra.Module
open import Data.Fin.Patterns
open import Data.Fin as F using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec.Functional
open import Vector.Structures

open import Algebra.BigOps
import Algebra.Module.Definition as MDef

open CommutativeRing cRing renaming (Carrier to A) hiding (zero)
open VRing rawRing using (_∙ⱽ_; _*ⱽ_)

-- open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid
open import Algebra.Module.Instances.FunctionalVector ring using (leftModule)
open import Algebra.Module.Instances.CommutativeRing cRing
open module CR n = CommutativeRing (*ⱽ-commutativeRing n) renaming (Carrier to F) using ()
open module MProps {n} = MProps′ cRing (leftModule n)
open module LM′ {n} = LeftModule (leftModule n) public renaming (Carrierᴹ to M)
open module MDef′ {n} = MDef (leftModule n)
import Relation.Binary.Reasoning.Setoid setoid as ≈-Reasoning

open SumRing ring
module ∑ {n} = SumRing (CR.ring n)
open ≈-Reasoning

private variable
  m n : ℕ
  xs ys zs : Vector M n
  α : F n

∑∑≈∑ : ∀ (xs : Vector (F m) n) i → ∑.∑ xs i ≈ ∑ (λ j → xs j i)
∑∑≈∑ {suc m} {zero} xs i = refl
∑∑≈∑ {suc m} {suc n} xs i = +-congˡ (∑∑≈∑ (tail xs) i)

∑∑≈∑∑′ : ∀ (xs : Vector (F m) n) → ∑ (λ j → ∑ λ i → xs i j) ≈ ∑ λ i → ∑ (xs i)
∑∑≈∑∑′ {zero} {zero} xs = refl
∑∑≈∑∑′ {zero} {suc n} xs = begin
  0# ≈˘⟨ +-identityˡ _ ⟩
  0# + 0# ≈⟨ +-congˡ (∑∑≈∑∑′ (tail xs)) ⟩
  0# + ∑ (λ i → ∑ (tail xs i)) ∎
∑∑≈∑∑′ {suc m} {zero} xs = begin
  0# + ∑ (λ j → ∑ (λ i → xs i (F.suc j))) ≈⟨ +-congˡ (∑∑≈∑∑′ (λ i j → xs i (F.suc j))) ⟩
  0# + 0# ≈⟨ +-identityˡ _ ⟩
  0# ∎
∑∑≈∑∑′ {suc m} {suc n} xs = begin
  (xs 0F 0F + ∑ (λ i → xs (F.suc i) 0F)) + ∑ (λ j → ∑ (λ i → xs i (F.suc j)))
    ≈⟨ +-congˡ (∑∑≈∑∑′ (λ i j → xs i (F.suc j))) ⟩
  (xs 0F 0F + ∑ (λ i → xs (F.suc i) 0F)) + (∑ (λ j → xs 0F (F.suc j)) + ∑ (λ i → ∑ (λ j → xs (F.suc i) (F.suc j))))
    ≈⟨ solve 4 (λ a b c d → (a ⊕ b) ⊕ c ⊕ d ⊜ (a ⊕ c) ⊕ b ⊕ d) refl (xs 0F 0F) (∑ (λ i → xs (F.suc i) 0F)) (∑ (λ j → xs 0F (F.suc j))) (∑ (λ i → ∑ (λ j → xs (F.suc i) (F.suc j)))) ⟩
  (xs 0F 0F + ∑ (λ j → xs 0F (F.suc j))) + (∑ (λ i → xs (F.suc i) 0F) + ∑ (λ i → ∑ (λ j → xs (F.suc i) (F.suc j))))
    ≈˘⟨ +-congˡ (∑Split (λ i → xs (F.suc i) 0F) _) ⟩
  (xs 0F 0F + ∑ (λ j → xs 0F (F.suc j))) + ∑ (λ i → xs (F.suc i) 0F + ∑ (λ j → xs (F.suc i) (F.suc j))) ∎


∑∑≈∑∑ : ∀ (xs : Vector (F m) n) → ∑ (∑.∑ xs) ≈ ∑ λ i → ∑ (xs i)
∑∑≈∑∑ xs = begin
  ∑ (λ i → ∑.∑ xs i) ≈⟨ ∑Ext (λ i → ∑∑≈∑ xs i)  ⟩
  ∑ (λ j → ∑ λ i → xs i j) ≈⟨ ∑∑≈∑∑′ xs ⟩
  (∑ λ i → ∑ (xs i)) ∎

∑-flip-matrix≈ : ∀ (xs : Vector (F m) n) → ∑ (∑.∑ xs) ≈ ∑ (∑.∑ (λ i j → xs j i))
∑-flip-matrix≈ xs = begin
  ∑ (∑.∑ xs) ≈⟨ ∑∑≈∑∑ xs ⟩
  ∑ (λ i → ∑ (xs i)) ≈˘⟨ ∑∑≈∑∑′ xs ⟩
  ∑ (λ i → ∑ (λ j → xs j i)) ≈˘⟨ ∑∑≈∑∑ (λ j i → xs i j) ⟩
  ∑ (∑.∑ (λ i j → xs j i)) ∎

_isSolutionOf_ : F n → Vector M n → Set _
α isSolutionOf v  = ∀ k → α ∙ⱽ v k ≈ 0#

sameSolutions : xs ⊆ⱽ ys → α isSolutionOf ys → α isSolutionOf xs
sameSolutions {n} {xs} {ys} {α} xs⊆ys sol i = begin
  ∑ (α *ⱽ xs i) ≈˘⟨ ∑Ext {n} (λ j → *-congˡ (xs*ys≈x j)) ⟩
  ∑ (α *ⱽ ∑.∑ (λ k l → ws k * ys k l)) ≈⟨ ∑Ext {n} (λ j → ∑.∑Mulrdist {n} {n} α _ _) ⟩
  ∑ {n} (∑.∑ {n} {n} λ k l → α l * (ws k * ys k l)) ≈⟨
    ∑Ext {n} (∑.∑Ext {n} {n} λ k l → {!!}) ⟩
  ∑ {n} (∑.∑ {n} {n} λ k l → ws k * (α l * ys k l)) ≈⟨ {!!} ⟩
  -- {!!} ≈⟨ {!!} ⟩
  0# ∎

-- foldr _+_ 0#
-- (λ i₁ →
--    α i₁ *
--    foldr (λ xs₁ ys₁ i₂ → xs₁ i₂ + ys₁ i₂) (λ _ → 0#)
--    (λ i₂ x → ws i₂ * ys i₂ x) i₁)

  -- {!begin
  -- ∑ (α *ₗ xs i) ≈˘⟨ ∑Ext (*ₗ-congˡ xs*ys≈x) ⟩
  -- ∑ (α *ₗ ∑.∑ (ws *ᵣ ys)) ≈⟨ ∑Ext (∑Mulrdist‵ α (ws *ᵣ ys)) ⟩
  -- ∑ (∑.∑ (λ j → α *ₗ (ws j *ₗ ys j))) ≈˘⟨ ∑Ext (∑.∑Ext λ j → *ₗ-assoc α (ws j) (ys j)) ⟩
  -- ∑ (∑.∑ (λ j → _ *ₗ ys j)) ≈⟨ ∑Ext {n} (∑.∑Ext {n} (λ j → *ₗ-congʳ λ _ → *-comm _ (ws j _))) ⟩
  -- ∑ (∑.∑ (λ j → _ *ₗ ys j)) ≈⟨ ∑Ext (∑.∑Ext (λ j → *ₗ-assoc (ws j) _ _)) ⟩
  -- ∑ (∑.∑ (λ j → ws j *ₗ (α *ₗ ys j))) ≈⟨ {!!} ⟩
  -- -- {!!} ≈⟨ {!!} ⟩
  -- 0# ∎!}
  where
  open _reaches_ (xs⊆ys (xsReachesItself xs i)) renaming (ys to ws)
