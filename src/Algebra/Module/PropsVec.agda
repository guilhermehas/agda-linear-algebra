open import Algebra

module Algebra.Module.PropsVec
  {rr ℓr}
  (cRing : CommutativeRing rr ℓr)
  where

import Algebra.Module.Props as MProps′
open import Algebra.Module
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Vec.Functional

open import Algebra.BigOps
import Algebra.Module.Definition as MDef

open CommutativeRing cRing renaming (Carrier to A)

open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open import Algebra.Module.Instances.CommutativeRing cRing
open module CR n = CommutativeRing (*ⱽ-commutativeRing n) renaming (Carrier to F) using ()
open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)
open module LM′ {n} = LeftModule (leftModule n) public renaming (Carrierᴹ to M)
open module MDef′ {n} = MDef (leftModule n)
import Relation.Binary.Reasoning.Setoid setoid as ≈-Reasoning

open SumRing ring
module ∑ {n} = SumRing (CR.ring n)
open ≈-Reasoning

private variable
  n : ℕ
  xs ys zs : Vector M n
  α : F n

_isSolutionOf_ : F n → Vector M n → Set _
α isSolutionOf v  = ∀ k → ∑ (α *ₗ v k) ≈ 0#

sameSolutions : xs ⊆ⱽ ys → α isSolutionOf ys → α isSolutionOf xs
sameSolutions {n} {xs} {ys} {α} xs⊆ys sol i = begin
  ∑ (α *ₗ xs i) ≈˘⟨ ∑Ext (*ₗ-congˡ xs*ys≈x) ⟩
  ∑ (α *ₗ ∑.∑ (ws *ᵣ ys)) ≈⟨ ∑Ext (∑Mulrdist‵ α (ws *ᵣ ys)) ⟩
  ∑ (∑.∑ (λ j → α *ₗ (ws j *ₗ ys j))) ≈˘⟨ ∑Ext (∑.∑Ext λ j → *ₗ-assoc α (ws j) (ys j)) ⟩
  ∑ (∑.∑ (λ j → _ *ₗ ys j)) ≈⟨ ∑Ext {n} (∑.∑Ext {n} (λ j → *ₗ-congʳ λ _ → *-comm _ (ws j _))) ⟩
  ∑ (∑.∑ (λ j → _ *ₗ ys j)) ≈⟨ ∑Ext (∑.∑Ext (λ j → *ₗ-assoc (ws j) _ _)) ⟩
  ∑ (∑.∑ (λ j → ws j *ₗ (α *ₗ ys j))) ≈⟨ {!!} ⟩
  -- {!!} ≈⟨ {!!} ⟩
  0# ∎
  where
  open _reaches_ (xs⊆ys (xsReachesItself xs i)) renaming (ys to ws)
