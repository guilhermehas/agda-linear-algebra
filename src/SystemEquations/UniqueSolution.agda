open import Algebra.DecidableField

module SystemEquations.UniqueSolution {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product
open import Data.Maybe using (Is-just; Maybe; just; nothing)
open import Data.Sum renaming ([_,_] to [_∙_])
open import Data.Empty
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Nat.Properties as ℕ using (module ≤-Reasoning)
open import Data.Fin as F using (Fin; suc; splitAt; fromℕ; toℕ; inject₁)
open import Data.Fin.Properties as F
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Nullary

open import Fin.Base
open import Fin.Properties
open import Vector.Structures
open import Vector.Properties
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
open import MatrixFuncNormalization.Definitions dField
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps′
open import Algebra.BigOps

open DecidableField dField renaming (Carrier to F) hiding (sym)
open CommutativeRing commutativeRing using (rawRing; ring; sym)
open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing
open import Algebra.Properties.Ring ring
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing using (Matrix; _++v_)
open import Algebra.Module.Instances.CommutativeRing commutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; subst; subst₂; cong)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid hiding (id)
open import Algebra.Module.PropsVec commutativeRing
open import SystemEquations.VecPiv dField
open import MatrixFuncNormalization.MainTheo dField
open import SystemEquations.Solving dField

open import lbry

open SumRing ring using (∑Ext; ∑0r; δ; ∑Mul1r; ∑Split)
open MDef′
open MProps

private variable
  m n p q : ℕ

private
  lemma-a : ∀ {a b} → a * (- b) + b * a ≈ 0#
  lemma-a = trans (+-congʳ (trans (*-comm _ _) (sym (-‿distribˡ-* _ _)))) (-‿inverseˡ _)

module _ where
  open SystemEquations
  open _≋ⱽ_

  sameSolutions≈ : {sx : SystemEquations n m} {sy : SystemEquations p m}
    → A++b sy ≋ⱽ A++b sx → Solution sx → Solution sy
  sameSolutions≈ sy≋ⱽsx (noSol f) = noSol (f ∘ sameSolutionsS (sy≋ⱽsx .bwd) _)
  sameSolutions≈ {sx = sx} {sy} sy≋ⱽsx (sol _ _ (f , g)) = sol
    _ _ (sameSolutionsS (sy≋ⱽsx .fwd) _ ∘ f , g ∘ sameSolutionsS (sy≋ⱽsx .bwd) _)

solveNormedEquationUnique : ∀ (sx : SystemEquations n m) (open SystemEquations sx)
  → MatrixIsNormed≁0≈1 A → ∃ IsSolutionAndUnique
solveNormedEquationUnique {n} {m} sx ANormed = vAffine , vAffFamily , sameSolution
  where
  open SolvingNormedEquation sx ANormed

  sameSolution : SameSolution vAffine
  sameSolution {vSol} isSol = vecSol , vecSol≈vSol
    where

    vecSol : ∀ i → F
    vecSol = vSol ∘ pivRes

    vPivSame : ∀ i → Affine.eval (vAffine (pivs i)) vecSol ≈ vSol (pivs i)
    vPivSame i rewrite vSplit′-same pivs i pivsCrescent = begin
      ∑ {m ∸ n} (λ j → vSol _ * - A i (pivRes j)) + b i ≈˘⟨ +-congˡ (isSol i) ⟩
      _ + ∑ {m} (λ j → A i j * vSol j) ≈˘⟨ +-congˡ (∑-pivs′-same pivs _ pivsCrescent) ⟩
      _ + (∑ (λ j → A i (pivs j) * vSol (pivs j)) + ∑ {m ∸ n}  (λ j → A i (pivRes j) * vSol (pivRes j)))
        ≈⟨ +-congˡ (+-comm _ _) ⟩
      _ + (_ + _) ≈˘⟨ +-assoc _ _ _ ⟩
      _ + _ + _ ≈˘⟨ +-congʳ (∑Split {m ∸ n} _ _) ⟩
      ∑ {m ∸ n} (λ j → vSol (pivRes j) * - A i (pivRes j) + A i (pivRes j) * vSol (pivRes j)) + _
        ≈⟨ +-congʳ (∑Ext {m ∸ n} λ _ → lemma-a ) ⟩
      _ + _ ≈⟨ +-congʳ (∑0r (m ∸ n)) ⟩
      0# + _ ≈⟨ +-identityˡ _ ⟩
      ∑ (λ j → A i (pivs j) * vSol (pivs j)) ≈⟨ ∑Ext (λ j → *-congʳ (AiPj≈δij i j)) ⟩
      ∑ (λ j → δ i j * vSol (pivs j)) ≈⟨ ∑Mul1r _ i ⟩
      vSol _ ∎

    vRPivSame : ∀ i → Affine.eval (vAffine (pivRes i)) vecSol ≈ vSol (pivRes i)
    vRPivSame i rewrite vSplit′-rPivs pivs i pivsCrescent = begin
      ∑ {m ∸ n} (λ j → _ * _) + 0# ≈⟨ +-identityʳ _ ⟩
      ∑ {m ∸ n} (λ j → _ * δ i j)  ≈⟨ ∑Ext (λ j → *-comm _ (δ i j)) ⟩
      ∑ {m ∸ n} (λ j → δ i j * _)  ≈⟨ ∑Mul1r _ i ⟩
      vSol _ ∎


    vecSol≈vSol : (i : Fin m) → Affine.eval (vAffine i) vecSol ≈ vSol i
    vecSol≈vSol i with ∃-piv⊎pivRes′ pivs pivsCrescent i
    ... | inj₁ (x , x≡piv) rewrite ≡.sym x≡piv = vPivSame _
    ... | inj₂ (x , x≡rPiv) rewrite ≡.sym x≡rPiv = vRPivSame _

solveNormedEquationNormUnique : ∀ (sx : SystemEquations n m) (open SystemEquations sx) → MatrixIsNormed≁0≈1 A++b
  → Solution
solveNormedEquationNormUnique sx norm with
  systemNormedSplit sx norm |
  systemUnsolvable {sx = sx} |
  solveNormedEquationUnique sx
... | inj₁ x | b | _ = SystemEquations.noSol $ b x
... | inj₂ y | _ | c = SystemEquations.sol _ _ $ proj₂ $ c y

solveUniqueSystemEquations : (sx : SystemEquations n m) (open SystemEquations sx) → Solution
solveUniqueSystemEquations sx = sameSolutions≈ A++b≋ⱽs sol-prob
  where
  open SystemEquations sx
  open FromNormalization≁0≈1 (normalize≈1≁0 A++b)

  sYs = A++b⇒systemEquations ys

  open SystemEquations sYs using ()
    renaming (Solution to SYs; A++b to A++b-ys)

  ys≋A++b-ys : ∀ i j → ys i j ≈ A++b-ys i j
  ys≋A++b-ys i j = reflexive (≡.sym (same-take ys i j))

  A++b≋ⱽs : A++b ≋ⱽ A++b-ys
  A++b≋ⱽs = ≋ⱽ-trans xs≋ⱽys $ ≋ⱽ-reflexive ys≋A++b-ys

  sol-prob = solveNormedEquationNormUnique sYs $ ≈-norm ys≋A++b-ys ysNormed
