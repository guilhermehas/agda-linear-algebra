module Rational.Properties where

open import Level using (0ℓ)
open import Function
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary.Decidable.Core
open import Algebra
open import Algebra.Apartness
open import Algebra.Field
open import Algebra.DecidableField
open import Algebra.Apartness

private variable
  p q : ℚᵘ

inv : (p : ℚᵘ) → p ≄ 0ℚᵘ → ℚᵘ
inv p p≠0 = 1/_ p ⦃ ≢-nonZero p≠0 ⦄

+-*-inv-isField : IsField _≃_ 0ℚᵘ 1ℚᵘ -_ _+_ _*_ inv
+-*-inv-isField = record
  { isCommutativeRing = +-*-isCommutativeRing
  ; hasInverse = λ x x≭0 → *-inverseʳ x ⦃ ≢-nonZero x≭0 ⦄
  ; 0≢1 = from-no (0ℚᵘ ≃? 1ℚᵘ)
  }

ℚᵘ-Field : Field _ _
ℚᵘ-Field = record { isField = +-*-inv-isField }

0ℚᵘ≠1ℚᵘ : 0ℚᵘ ≄ 1ℚᵘ
0ℚᵘ≠1ℚᵘ = from-no (0ℚᵘ ≃? 1ℚᵘ)

_≠?_ : Decidable _≄_
x ≠? y = ¬? (x ≃? y)

open HeytingField +-*-heytingField renaming (Carrier to F) hiding (refl)

+-*-decidableField : DecidableField _ _ _
+-*-decidableField = record { isDecidableField = record { isHeytingField = isHeytingField ; decidableInequality = _≠?_ }}
