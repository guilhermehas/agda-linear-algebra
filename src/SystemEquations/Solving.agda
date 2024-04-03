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
open import Data.Fin as F using (Fin; suc; splitAt; fromℕ)
open import Data.Fin.Properties as F
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Nullary

open import Vector.Structures
open import Vector.Properties
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
open import MatrixFuncNormalization.Definitions dField
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
open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid hiding (id)
open import Algebra.Module.PropsVec commutativeRing hiding (module MProps)

open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)
open SumRing ring using (∑Ext; ∑0r)
open MDef′

private variable
  m n : ℕ

private
  lastFin : (n : ℕ) → Fin (n ℕ.+ 1)
  lastFin ℕ.zero = 0F
  lastFin (ℕ.suc n) = suc (lastFin n)

  injF : Fin n → Fin (n ℕ.+ 1)
  injF 0F = 0F
  injF (suc i) = suc (injF i)

  add-1 : Vector F n → Vector F (ℕ.suc n)
  add-1 xs = appendLast xs (- 1#)

A++b⇒systemEquations : Matrix F n (m ℕ.+ 1) → SystemEquations n m
A++b⇒systemEquations xs = record { A = λ i j → xs i (injF j) ; b = λ i → xs i (lastFin _) }

module _ where
  open SystemEquations

  sameSolutionsSE : {sx sy : SystemEquations n m}  → A++b sy ⊆ⱽ A++b sx
    → ∀ v → IsSolutionA++b sx v → IsSolutionA++b sy v
  sameSolutionsSE sy⊆ⱽsx i = sameSolutions {α = i} sy⊆ⱽsx

tail-lemma : ∀ (u : Vector F (ℕ.suc n)) b k → tail (appendLast u b) k ≈ (appendLast (tail u) b) k
tail-lemma u b k = refl

add-1∑ : ∀ (v : Vector F n) b (u : Vector F n) → (add-1 v ∙ⱽ appendLast u b) ≈ u ∙ⱽ v - b
add-1∑ {ℕ.zero} v b u = begin
  - 1# * b + 0# ≈⟨ +-identityʳ _ ⟩
  - 1# * b      ≈⟨ -1*x≈-x _ ⟩
  - b          ≈˘⟨ +-identityˡ (- b) ⟩
  0# + - b ∎
add-1∑ {ℕ.suc n} v b u = begin
  v 0F * u 0F + add-1 (tail v) ∙ⱽ tail (appendLast u b) ≈⟨ +-congʳ (*-comm _ _)⟩
  u 0F * v 0F + add-1 (tail v) ∙ⱽ appendLast (tail u) b ≈⟨ +-congˡ (add-1∑ _ b (tail u)) ⟩
  u 0F * v 0F + (tail u ∙ⱽ tail v - b)             ≈˘⟨ +-assoc _ _ (- b) ⟩
  u 0F * v 0F + tail u ∙ⱽ tail v - b ∎

sameSolutionsA++b : ∀ {sx : SystemEquations n m} {v} (open SystemEquations sx)
  → IsSolutionA++b $ add-1 v → IsSolution v
sameSolutionsA++b {n = n} {m = m} {sx = system A b} {v} sv i = begin
  A i ∙ⱽ v ≈⟨ +-inverseˡ-unique (A i ∙ⱽ v) (- b i) sv-lemma ⟩
  - - b i  ≈⟨ -‿involutive _ ⟩
  b i ∎
  where

  sv-lemma = begin
    A i ∙ⱽ v - b i             ≈˘⟨ add-1∑ v (b i) (A i) ⟩
    add-1 v ∙ⱽ appendLast (A i) (b i) ≈⟨ sv i ⟩
    0# ∎

sameSolutionsA++b-inv : ∀ {sx : SystemEquations n m} {v} (open SystemEquations sx)
  → IsSolution v → IsSolutionA++b $ add-1 v
sameSolutionsA++b-inv {m = m} {system A b} {v} sv i = begin
  add-1 v ∙ⱽ appendLast (A i) (b i) ≈⟨ add-1∑ v _ _ ⟩
  A i ∙ⱽ v - b i                    ≈⟨ +-congʳ (sv i) ⟩
  b i - b i                         ≈⟨ -‿inverseʳ (b i) ⟩
  0# ∎

systemUnsolvable : ∀ {sx : SystemEquations n m} (open SystemEquations sx) → A≈0∧b#0 → ∀ {v} → IsSolution v → ⊥
systemUnsolvable {n = n} {m} {system A b} (i , A0 , b#0) {v} sv = tight _ _ .proj₂
  (begin
    b i             ≈˘⟨ sv i ⟩
    A i ∙ⱽ v         ≈⟨ ∑Ext (λ j → trans (*-congʳ (A0 j)) (zeroˡ _)) ⟩
    ∑ {m} 0ⱽ ≈⟨ ∑0r m ⟩
    0# ∎) b#0

module _ where
  open MatrixIsNormed≁0≈1
  open MatrixIsNormed≁0

  emptyNormed : (A : Matrix F 0 n) → MatrixIsNormed≁0≈1 A
  pivs (isNormed (emptyNormed A)) ()
  mPivots (isNormed (emptyNormed A)) ()
  pivsCrescent (isNormed (emptyNormed A)) {y = ()} x
  columnsZero (isNormed (emptyNormed A)) () j x
  pivsOne (emptyNormed A) ()

systemNormedSplit : ∀ (sx : SystemEquations n m) (open SystemEquations sx) → MatrixIsNormed≁0≈1 A++b
  → A≈0∧b#0 ⊎ MatrixIsNormed≁0≈1 A
systemNormedSplit {ℕ.zero} sx normed = inj₂ (emptyNormed _)
systemNormedSplit {ℕ.suc n} {m} (system A b) (cIsNorm≁0≈1 (cIsNorm≁0 pivs mPivots pivsCrescent columnsZero) pivsOne)
  with pivs (fromℕ n) F.≟ fromℕ m
... | yes p = inj₁ (fromℕ _ , (λ i → A≈0 (mPivots (fromℕ n) .proj₂ (F.inject₁ i) (inj₁< i)))  , (b#0 $ mPivots (fromℕ _) .proj₁))
  where
  b#0 : appendLast (A $ fromℕ n) (b $ fromℕ n) (pivs $ fromℕ n) # 0# → b (fromℕ n) # 0#
  b#0 rewrite p | appendLastFromℕ (A $ fromℕ n) (b $ fromℕ n) = id

  A≈0 : {i : Fin _} → appendLast (A (fromℕ n)) (b (fromℕ n)) (F.inject₁ i) ≈ 0# → A (fromℕ n) i ≈ 0#
  A≈0 {i} rewrite appendLastInj (A (fromℕ n)) (b (fromℕ n)) i = id

  inj₁< : ∀ i → F.inject₁ i F.< pivs (fromℕ n)
  inj₁< i = ≡.subst (λ x → F.inject₁ i F.< x) (≡.sym p) (≤∧≢⇒< (≤fromℕ _) (fromℕ≢inject₁ ∘ ≡.sym))
... | no ¬p = {!!}
