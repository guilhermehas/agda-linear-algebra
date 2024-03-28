open import Algebra.DecidableField

module SystemEquations.Solving {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function
open import Data.Product
open import Data.Maybe using (Is-just; Maybe; just; nothing)
open import Data.Sum
open import Data.Empty
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as F using (Fin; suc; splitAt)
open import Data.Fin.Patterns
open import Data.Vec.Functional

open import Vector.Structures
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps′
open import Algebra.BigOps

open DecidableField dField renaming (Carrier to F) hiding (sym)
open HeytingField heytingField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring; sym; +-commutativeMonoid)
open import Algebra.Properties.Ring ring
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing using (Matrix)
open import Algebra.Module.Instances.CommutativeRing commutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid

open module MD {n} = MDefinition (leftModule n)
open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)
open SumRing ring using (∑Ext; ∑0r)

private variable
  m n : ℕ

private
  lastFin : (n : ℕ) → Fin (n ℕ.+ 1)
  lastFin ℕ.zero = 0F
  lastFin (ℕ.suc n) = suc (lastFin n)

  injF : Fin n → Fin (n ℕ.+ 1)
  injF 0F = 0F
  injF (suc i) = suc (injF i)

  add-1 : Vector F n → Vector F (n ℕ.+ 1)
  add-1 {ℕ.zero} v _ = - 1#
  add-1 {ℕ.suc n} v 0F = v 0F
  add-1 {ℕ.suc n} v (suc i) = add-1 (tail v) i

  splitAt-1-inj₁ : ∀ (v : Vector F n) i j → splitAt n i ≡ inj₁ j → (add-1 v) i ≡ v j
  splitAt-1-inj₁ {ℕ.suc n} v 0F 0F eqn = ≡.refl
  splitAt-1-inj₁ {ℕ.suc n} v (suc i) 0F eqn with splitAt n i
  splitAt-1-inj₁ {ℕ.suc n} v (suc i) 0F () | inj₁ x
  splitAt-1-inj₁ {ℕ.suc n} v (suc i) 0F () | inj₂ y
  splitAt-1-inj₁ {ℕ.suc n} v (suc i) (suc j) eqn with splitAt n i in eqn
  splitAt-1-inj₁ {ℕ.suc n} v (suc i) (suc .x) ≡.refl | inj₁ x = splitAt-1-inj₁ (tail v) i _ eqn

  splitAt-1-inj₂ : ∀ (v : Vector F n) i j → splitAt n i ≡ inj₂ j → (add-1 v) i ≡ - 1#
  splitAt-1-inj₂ {ℕ.zero} v i .i ≡.refl = ≡.refl
  splitAt-1-inj₂ {ℕ.suc n} v (suc i) 0F x with splitAt n i in eqn
  splitAt-1-inj₂ {ℕ.suc n} v (suc i) 0F ≡.refl | inj₂ .0F = splitAt-1-inj₂ (tail v) i 0F eqn


A++b⇒systemEquations : Matrix F n (m ℕ.+ 1) → SystemEquations n m
A++b⇒systemEquations xs = record { A = λ i j → xs i (injF j) ; b = λ i → xs i (lastFin _) }

module _ where
  open SystemEquations

  sameSolutionsSE : {sx sy : SystemEquations n m}  → A++b sy ⊆ⱽ A++b sx
    → ∀ v → IsSolutionA++b sx v → IsSolutionA++b sy v
  sameSolutionsSE sy⊆ⱽsx _ = sameSolutions sy⊆ⱽsx

tail-lemma : ∀ (u : Vector F (ℕ.suc n)) b k → tail (u ++ [ b ]) k ≈ (tail u ++ [ b ]) k
tail-lemma {n} _ _ k with splitAt n k
... | inj₁ _ = refl
... | inj₂ _ = refl

add-1∑ : ∀ (v : Vector F n) b (u : Vector F n) → (add-1 v ∙ⱽ (u ++ [ b ])) ≈ u ∙ⱽ v - b
add-1∑ {ℕ.zero} v b u = begin
  - 1# * b + 0# ≈⟨ +-identityʳ _ ⟩
  - 1# * b      ≈⟨ -1*x≈-x _ ⟩
  - b          ≈˘⟨ +-identityˡ (- b) ⟩
  0# + - b ∎
add-1∑ {ℕ.suc n} v b u = begin
  v 0F * u 0F + add-1 (tail v) ∙ⱽ tail (u ++ [ b ]) ≈⟨ +-cong (*-comm _ _)
    (∑Ext {n ℕ.+ 1} λ j → *-congˡ (tail-lemma u b j)) ⟩
  u 0F * v 0F + add-1 (tail v) ∙ⱽ (tail u ++ [ b ]) ≈⟨ +-congˡ (add-1∑ _ b (tail u)) ⟩
  u 0F * v 0F + (tail u ∙ⱽ tail v - b)             ≈˘⟨ +-assoc _ _ (- b) ⟩
  u 0F * v 0F + tail u ∙ⱽ tail v - b ∎

sameSolutionsA++b : ∀ {sx : SystemEquations n m} {v}
  (open SystemEquations sx)
  → IsSolutionA++b $ add-1 v → IsSolution v
sameSolutionsA++b {n = n} {m = m} {sx = system A b} {v} sv i = begin
  A i ∙ⱽ v ≈⟨ +-inverseˡ-unique (A i ∙ⱽ v) (- b i) sv-lemma ⟩
  - - b i  ≈⟨ -‿involutive _ ⟩
  b i ∎
  where

  sv-lemma = begin
    A i ∙ⱽ v - b i             ≈˘⟨ add-1∑ v (b i) (A i) ⟩
    add-1 v ∙ⱽ (A i ++ [ b i ]) ≈⟨ ∑Ext (sv i) ⟩
    ∑ {m ℕ.+ 1} 0ⱽ              ≈⟨ ∑0r (m ℕ.+ 1) ⟩
    0# ∎

sameSolutionsA++b-inv : ∀ {sx : SystemEquations n m} {v}
  (open SystemEquations sx)
  → IsSolution v → IsSolutionA++b $ add-1 v
sameSolutionsA++b-inv {m = m} {system A b} {v} sv i j with splitAt m j in eqn
... | inj₁ k rewrite splitAt-1-inj₁ v j k eqn = {!!}
... | inj₂ k rewrite splitAt-1-inj₂ v j k eqn = {!sv i!}

  -- begin
  -- add-1 v j * (A i ++ [ b i ]) j ≈⟨ {!!} ⟩
  -- -- {!!} ≈⟨ {!!} ⟩
  -- 0# ∎


systemUnsolvable : ∀ {sx : SystemEquations n m} (open SystemEquations sx) i → A i ≋ 0ⱽ → b i # 0#
  → ∀ {v} → IsSolution v → ⊥
systemUnsolvable {n = n} {m} {system A b} i A0 b#0 {v} sv = tight _ _ .proj₂
  (begin
    b i             ≈˘⟨ sv i ⟩
    A i ∙ⱽ v         ≈⟨ ∑Ext (λ j → trans (*-congʳ (A0 j)) (zeroˡ _)) ⟩
    ∑ {m} 0ⱽ ≈⟨ ∑0r m ⟩
    0# ∎) b#0
