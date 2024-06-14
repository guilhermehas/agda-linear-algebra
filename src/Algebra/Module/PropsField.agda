open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function

module Algebra.Module.PropsField
  {c ℓ₁ ℓ₂ mr ℓm}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (leftModule : LeftModule (CommutativeRing.ring
    $ HeytingCommutativeRing.commutativeRing
    $ HeytingField.heytingCommutativeRing hField) mr ℓm)
  where

open import Data.Bool hiding (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; _≟_)
open import Data.Product
open import Data.Vec.Functional
open import Data.Vec.Functional.Properties
open import Relation.Unary.Properties

open import Algebra.Module.DefsField hField leftModule
open import Algebra.BigOps
open import Vector.Base
open import Vector.Properties
open import Vector.Structures

open HeytingField hField renaming (Carrier to A) hiding (sym)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open CommutativeRing commutativeRing using (rawRing; *-commutativeMonoid; ring; sym)
open LeftModule leftModule renaming (Carrierᴹ to M)
open SumCommMonoid +ᴹ-commutativeMonoid
open VRing rawRing using (_*ⱽ_)
import Algebra.Solver.CommutativeMonoid *-commutativeMonoid as *-Solver hiding (_≟_)
import Algebra.Solver.CommutativeMonoid +ᴹ-commutativeMonoid as +-Solver hiding (_≟_)
open import Algebra.HeytingCommutativeRing.Properties heytingCommutativeRing
open import Algebra.Module.Base ring
open import Algebra.Module.Props commutativeRing leftModule public
open import Algebra.Module.VecSpace leftModule
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

import Relation.Binary.Reasoning.Setoid as RSetoid
module ≈-Reasoning = RSetoid setoid

private variable
  n : ℕ
  xs ys : Vector M n


*#0⊆ⱽ : ∀ (xs : Vector M n) {ys : Vector A n} (ys#0 : ∀ i → ys i # 0#) → xs ⊆ⱽ ys *ᵣ xs
*#0⊆ⱽ {n} xs {ys} ys#0 {x} (zs by xs*zs≈x) = as by ∑as*zs≈x
  where
  ass : _ → _
  ass i = #0⇒invertible (ys#0 i) .proj₁
  as = ass *ⱽ zs

  module _ (i : Fin n) where
    open *-Solver
    x⁻¹ = #0⇒invertible (ys#0 i) .proj₁
    x⁻¹≈ys = #0⇒invertible (ys#0 i) .proj₂ .proj₁

    as*ys≈zs : as i * ys i ≈ zs i
    as*ys≈zs = begin
      ass i * zs i * ys i ≈⟨ solve 3 (λ a b c → (a ⊕ b) ⊕ c ⊜ (a ⊕ c) ⊕ b) refl (ass i) (zs i) (ys i) ⟩
      x⁻¹   * ys i * zs i ≈⟨ *-congʳ x⁻¹≈ys ⟩
      1# * zs i           ≈⟨ *-identityˡ _ ⟩
      zs i ∎
      where open ≈-Reasoning

    as≈xs : as i *ₗ (ys i *ₗ xs i) ≈ᴹ zs i *ₗ xs i
    as≈xs = begin
        as i *ₗ ys i *ₗ xs i ≈˘⟨ *ₗ-assoc _ _ _ ⟩
        (as i * ys i) *ₗ xs i ≈⟨ *ₗ-congʳ as*ys≈zs ⟩
        zs i *ₗ xs i ∎ where open ≈ᴹ-Reasoning

  ∑as*zs≈x = begin
    ∑ (as *ᵣ (ys *ᵣ xs)) ≈⟨ ∑Ext {n} as≈xs ⟩
    ∑ (zs *ᵣ xs)         ≈⟨ xs*zs≈x ⟩
    x ∎ where open ≈ᴹ-Reasoning

*ₗ#0⊆ⱽ : (xs : Vector M n) (ys : Vector A n) → ys *ᵣ xs ⊆ⱽ xs
*ₗ#0⊆ⱽ {n} xs ys {x} (ws by xs*ws≈x) = as by as*xs≈x
  where
  open ≈ᴹ-Reasoning
  as = ws *ⱽ ys
  as*xs≈x = begin
    ∑ ((ws *ⱽ ys) *ᵣ xs) ≈⟨ ∑Ext {n} (λ _ → *ₗ-assoc _ _ _) ⟩
    ∑ (ws *ᵣ (ys *ᵣ xs)) ≈⟨ xs*ws≈x ⟩
    x ∎

*#0≈ⱽ : ∀ (xs : Vector M n) {ys : Vector A n} (ys#0 : ∀ i → ys i # 0#) → xs ≋ⱽ (ys *ᵣ xs)
*#0≈ⱽ xs ys#0 = record { fwd = *#0⊆ⱽ xs ys#0 ; bwd = *ₗ#0⊆ⱽ xs _ }

linInd→¬linDep : IsLinearIndependent xs → ¬ IsLinearDependent xs
linInd→¬linDep linIndep (reach , i , ysI#0) = tight _ _ .proj₂ (linIndep reach i) ysI#0

private
  _[_]←₂_*[_] : Vector A n → Fin n → A → Fin n → Vector A n
  (M [ q ]←₂ r *[ p ]) i with does (q ≟ i)
  ... | true = M i + r * M p
  ... | false = M i


-- sameLinInd : (xs ys : Vector M n) → xs ≈ⱽ ys → ∀ b
--   → LinearIndependent? xs b → LinearIndependent? ys b
-- sameLinInd {n} xs ys (idR xs≋ys) false (linDep (ws by xs*ws≈x , i , ws#0)) = linDep
--   $ ws by ≈ᴹ-trans (∑Ext (*ₗ-congˡ ∘ ≈ᴹ-sym ∘ xs≋ys)) xs*ws≈x , i , ws#0
-- sameLinInd {n} xs ys (rec {ys = zs} (swapOp p q p≢q) xs≈ⱽzs same) false dep@(linDep (ws by xs*ws≈x , i , ws#0))
--   with linDep (wws by xs*wws≈x , j , wws#0) ← sameLinInd _ _ xs≈ⱽzs false dep
--   = linDep $ (swapV wws p q by ≈ᴹ-trans ∑Same xs*wws≈x) , ∃#0
--   where
--   open ≈ᴹ-Reasoning


--   sameness : ∀ i → swapV wws p q i *ₗ ys i ≈ᴹ swapV (wws *ᵣ zs) p q i
--   sameness i =
--     begin
--     swapV wws p q i *ₗ ys i          ≈˘⟨ *ₗ-congˡ (same i) ⟩
--     swapV wws p q i *ₗ swapV zs p q i ≈⟨ help ⟩
--     swapV (wws *ᵣ zs) p q i ∎ where

--     help : _
--     help with i ≟ p | i ≟ q
--     ... | no i≢p | no i≢q = begin
--       _  ≈⟨ *ₗ-cong (reflexive (swap-diff wws i i≢p i≢q)) $ ≈ᴹ-reflexive $ swap-diff _ i i≢p i≢q ⟩
--       _ ≡˘⟨ swap-diff (wws *ᵣ zs) _ i≢p i≢q ⟩
--       swapV (wws *ᵣ zs) p q i ∎
--     ... | no i≢p | yes ≡.refl = begin
--       _ ≈⟨ *ₗ-cong (reflexive $ updateAt-updates i _) (≈ᴹ-reflexive $ updateAt-updates q _) ⟩
--       wws p *ₗ zs p ≡˘⟨ updateAt-updates q _ ⟩
--       swapV (wws *ᵣ zs) p q q ∎
--     ... | yes ≡.refl | no i≢q = begin
--       _ *ₗ _ ≈⟨ *ₗ-cong (reflexive (≡.trans (updateAt-minimal _ _ _ i≢q) (updateAt-updates p _)))
--         (≈ᴹ-reflexive (≡.trans (updateAt-minimal _ _ _ i≢q) (updateAt-updates p _))) ⟩
--       wws q *ₗ zs q ≡˘⟨ updateAt-updates p _ ⟩
--       _             ≡˘⟨ updateAt-minimal p q _ p≢q ⟩
--       swapV (wws *ᵣ zs) p q p ∎
--     ... | yes ≡.refl | yes ≡.refl = begin
--       _              ≈⟨ *ₗ-cong (reflexive (updateAt-updates p _)) (≈ᴹ-reflexive (updateAt-updates p _)) ⟩
--       wws p *ₗ zs p ≡˘⟨ updateAt-updates p _ ⟩
--       swapV (wws *ᵣ zs) p p p ∎

--   ∃#0 : _
--   ∃#0 with j ≟ p | j ≟ q
--   ... | yes ≡.refl | yes ≡.refl = p , #-congʳ (reflexive (≡.sym (updateAt-updates j _))) wws#0
--   ... | yes ≡.refl | no j≢q = q , #-congʳ (reflexive (≡.sym (updateAt-updates q _))) wws#0
--   ... | no j≢p | yes ≡.refl = p , #-congʳ (reflexive (≡.sym (≡.trans (updateAt-minimal _ _ _ (j≢p ∘ ≡.sym))
--     (updateAt-updates p _)))) wws#0
--   ... | no j≢p | no j≢q = _ , #-congʳ (reflexive (≡.sym (swap-diff _ _ j≢p j≢q))) wws#0

--   ∑Same : ∑ (swapV wws p q *ᵣ ys) ≈ᴹ ∑ (wws *ᵣ zs)
--   ∑Same = begin
--     ∑ (swapV wws p q *ᵣ ys) ≈⟨ ∑Ext sameness ⟩
--     ∑ (swapV (wws *ᵣ zs) p q) ≈⟨ ∑Swap _ p q ⟩
--     ∑ (wws *ᵣ zs) ∎

-- sameLinInd xs ys (rec {ys = zs} (addCons p q p≢q r) xs≈ⱽzs same) false dep@(linDep (ws by xs*ws≈x , i , ws#0))
--   with linDep (wws by xs*wws≈x , j , wws#0) ← sameLinInd _ _ xs≈ⱽzs false dep
--   = linDep (ks by ≈ᴹ-trans ∑Same xs*wws≈x , ∃#0)

--   where
--   open ≈ᴹ-Reasoning

--   q≢p = p≢q ∘ ≡.sym
--   v0 = - r
--   ks = wws [ q ]←₂ 0# *[ p ] [ p ]←₂ v0 *[ q ]
--   zsk = zs [ q ]← r *[ p ]
--   ksZs = ks *ᵣ zsk
--   wsZs = wws *ᵣ zs

--   genSum : (xs : Vector M _) → xs p +ᴹ xs q +ᴹ ∑ (xs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ)  ≈ᴹ ∑ xs
--   genSum xs = ≈ᴹ-sym (begin
--     ∑ xs ≈⟨ ∑Remove₂ xs p ⟩
--     xs p +ᴹ ∑ (xs [ p ]≔ 0ᴹ) ≈⟨ +ᴹ-congˡ (∑Remove₂ _ q) ⟩
--     xs p +ᴹ ((xs [ p ]≔ 0ᴹ) q +ᴹ ∑ (xs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) ) ≈˘⟨ +ᴹ-assoc _ _ _ ⟩
--     _ +ᴹ (xs [ p ]≔ 0ᴹ) q +ᴹ _ ≈⟨ +ᴹ-congʳ (+ᴹ-congˡ (≈ᴹ-reflexive (updateAt-minimal _ _ _ (p≢q ∘ ≡.sym)))) ⟩
--     _ +ᴹ xs q +ᴹ _ ∎)

--   sameInd : ∀ i → (ksZs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) i ≈ᴹ (wsZs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) i
--   sameInd i with i ≟ q | i ≟ p
--   ... | yes ≡.refl | _ = begin
--     _  ≡⟨ updateAt-updates q _ ⟩
--     _ ≡˘⟨ updateAt-updates q _ ⟩
--     _ ∎
--   ... | no i≢q | yes ≡.refl = begin
--     _  ≡⟨ updateAt-minimal _ _ _ i≢q ⟩
--     _  ≡⟨ updateAt-updates p _ ⟩
--     _ ≡˘⟨ updateAt-updates p _ ⟩
--     _ ≡˘⟨ updateAt-minimal _ _ _ i≢q ⟩
--     _ ∎
--   ... | no i≢q | no i≢p = begin
--     _  ≡⟨ updateAt-minimal _ _ _ i≢q ⟩
--     _  ≡⟨ updateAt-minimal _ _ _ i≢p ⟩
--     _  ≡⟨ help ⟩
--     _ ≡˘⟨ updateAt-minimal _ _ _ i≢p ⟩
--     _ ≡˘⟨ updateAt-minimal _ _ _ i≢q ⟩
--     _ ∎ where

--     help : ksZs i ≡ wsZs i
--     help rewrite dec-no (p ≟ i) (i≢p ∘ ≡.sym) | dec-no (q ≟ i) (i≢q ∘ ≡.sym) = ≡.refl

--   sameTwo : ksZs p +ᴹ ksZs q ≈ᴹ wsZs p +ᴹ wsZs q
--   sameTwo rewrite dec-yes (p ≟ p) ≡.refl .proj₂ | dec-yes (q ≟ q) ≡.refl .proj₂
--     | dec-no (q ≟ p) (p≢q ∘ ≡.sym) | dec-no (p ≟ q) p≢q | dec-yes (q ≟ q) ≡.refl .proj₂ = begin
--       (wws p + v0 * (wws q + 0# * wws p)) *ₗ zs p
--         +ᴹ (wws q + 0# * wws p) *ₗ (zs q +ᴹ r *ₗ zs p) ≈⟨ +ᴹ-cong (*ₗ-congʳ (+-congˡ (*-congˡ
--           (trans (+-congˡ (zeroˡ _)) (+-identityʳ _)))))
--           (*ₗ-congʳ (trans (+-congˡ (zeroˡ _)) (+-identityʳ _))) ⟩

--       (wws p + v0 * wws q) *ₗ zs p +ᴹ wws q *ₗ (zs q +ᴹ r *ₗ zs p) ≈⟨ +ᴹ-cong
--         (*ₗ-distribʳ _ _ _) (*ₗ-distribˡ _ _ _) ⟩

--       wws p *ₗ zs p +ᴹ (v0 * wws q) *ₗ zs p +ᴹ (wws q *ₗ zs q +ᴹ wws q *ₗ r *ₗ zs p) ≈⟨ +ᴹ-assoc _ _ _ ⟩
--       wws p *ₗ zs p +ᴹ ((v0 * wws q) *ₗ zs p +ᴹ (wws q *ₗ zs q +ᴹ wws q *ₗ r *ₗ zs p)) ≈⟨
--         +ᴹ-congˡ help ⟩
--       wws p *ₗ zs p +ᴹ wws q *ₗ zs q ∎

--       where
--       open +-Solver

--       help2 = begin
--         (v0 * wws q) *ₗ zs p +ᴹ wws q *ₗ r *ₗ zs p ≈˘⟨ +ᴹ-congˡ (*ₗ-assoc _ _ _) ⟩
--         (v0 * wws q) *ₗ zs p +ᴹ (wws q * r) *ₗ zs p ≈˘⟨ *ₗ-distribʳ _ _ _ ⟩
--         (v0 * wws q + wws q * r) *ₗ zs p ≈⟨ *ₗ-congʳ (trans (+-congˡ (*-comm _ _)) (trans
--           (trans (sym (distribʳ _ _ _)) (*-congʳ (-‿inverseˡ _))) (zeroˡ (wws q)))) ⟩
--         0# *ₗ zs p ≈⟨ *ₗ-zeroˡ _ ⟩
--         0ᴹ ∎

--       help = begin
--         (v0 * wws q) *ₗ zs p +ᴹ (wws q *ₗ zs q +ᴹ wws q *ₗ r *ₗ zs p) ≈⟨
--           solve 3 (λ a b c → (a ⊕ (b ⊕ c)) , ((a ⊕ c) ⊕ b)) ≈ᴹ-refl _ _ _ ⟩
--         ((v0 * wws q) *ₗ zs p +ᴹ wws q *ₗ r *ₗ zs p) +ᴹ wws q *ₗ zs q ≈⟨ +ᴹ-congʳ help2 ⟩
--         0ᴹ +ᴹ wws q *ₗ zs q ≈⟨ +ᴹ-identityˡ _ ⟩
--         wws q *ₗ zs q ∎

--   ∑Same = begin
--     ∑ (ks *ᵣ ys) ≈˘⟨ ∑Ext (*ₗ-congˡ ∘ same) ⟩
--     ∑ ksZs ≈˘⟨ genSum ksZs ⟩
--     ksZs p +ᴹ ksZs q +ᴹ ∑ (ksZs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) ≈⟨ +ᴹ-cong sameTwo (∑Ext sameInd) ⟩
--     -- {!!} ≈⟨ {!!} ⟩
--     wsZs p +ᴹ wsZs q +ᴹ ∑ (wsZs [ p ]≔ 0ᴹ [ q ]≔ 0ᴹ) ≈⟨ genSum wsZs ⟩
--     ∑ wsZs ∎


--   ∃#0 : _
--   ∃#0 with j ≟ p | j ≟ q
--   ... | yes ≡.refl | _ = p , #-congʳ {!!} {!!}
--   ... | no j≢p | yes ≡.refl = j , #-congʳ help wws#0
--     where
--     help : wws j ≈ ks j
--     help rewrite dec-no (p ≟ j) (j≢p ∘ ≡.sym)
--       | dec-yes (j ≟ j) ≡.refl .proj₂
--       = sym (trans (+-congˡ (zeroˡ _)) (+-identityʳ _))
--   ... | no j≢p | no j≢q = j , #-congʳ help wws#0
--     where
--     help : wws j ≈ ks j
--     help rewrite dec-no (p ≟ j) (j≢p ∘ ≡.sym) | dec-no (q ≟ j) (j≢q ∘ ≡.sym) = refl



-- sameLinInd xs ys xs≈ⱽys true (linInd ind) = {!!}
