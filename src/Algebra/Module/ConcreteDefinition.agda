open import Algebra

module Algebra.Module.ConcreteDefinition {rr ℓr} (ring : Ring rr ℓr) where

open import Data.Nat
open import Data.Fin using () renaming (suc to fsuc)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Data.Fin.Patterns
open import Algebra.Matrix.Structures

open Ring ring renaming (Carrier to A)
open import Algebra.Module.Instances.FunctionalVector ring
import Algebra.Module.Definition as MDef'

open module MDef {n} = MDef' (leftModule n)

open MRing rawRing

private variable
  m n : ℕ

IsCLinearIndependent : Matrix A n m → m ≤ 3 → Set ℓr
IsCLinearIndependent {ℕ.zero} {m = 0} xs z≤n = ⊤
IsCLinearIndependent {suc n} {m = 0} xs z≤n = ⊥
IsCLinearIndependent {ℕ.zero} {1} xs (s≤s z≤n) = ⊤
IsCLinearIndependent {1} {1} xs (s≤s z≤n) = xs 0F ≠0
IsCLinearIndependent {2+ n} {1} xs (s≤s z≤n) = ⊥
IsCLinearIndependent {m = 2} xs (s≤s (s≤s z≤n)) = {!!}
IsCLinearIndependent {m = 3} xs (s≤s (s≤s (s≤s z≤n))) = {!!}


IsCInd⇒Ind : (xs : Matrix A n m) (m≤3 : m ≤ 3) → IsCLinearIndependent xs m≤3 → IsLinearIndependent xs
IsCInd⇒Ind {ℕ.zero} {0} _ z≤n _ _ ()
IsCInd⇒Ind {suc n}  {0} _ z≤n () _ _
IsCInd⇒Ind {1} {1} xs m≤3 cLin ∑≈0 0F = {!!}
IsCInd⇒Ind {2+ n} {m = 1} xs m≤3 cLin ∑≈0 i = {!!}
IsCInd⇒Ind {suc n} {m = 2+ m} xs m≤3 cLin ∑≈0 i = {!!}
