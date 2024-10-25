module Rational.Properties where

open import Level using (0ℓ)
open import Function
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Rational
open import Data.Rational.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Relation.Nullary.Decidable.Core
open import Algebra
open import Algebra.Apartness
open import Algebra.Field
open import Algebra.DecidableField

private variable
  p q : ℚ

inv : (p : ℚ) → p ≢ 0ℚ → ℚ
inv p p≠0 = 1/_ p ⦃ ≢-nonZero p≠0 ⦄

0ℚ≠1ℚ : 0ℚ ≢ 1ℚ
0ℚ≠1ℚ = from-no (0ℚ ≟ 1ℚ)

+-*-inv-isField : IsField _≡_ 0ℚ 1ℚ -_ _+_ _*_ inv
+-*-inv-isField = record
  { isCommutativeRing = +-*-isCommutativeRing
  ; hasInverse = λ x x≭0 → *-inverseʳ x ⦃ ≢-nonZero x≭0 ⦄
  ; 0≢1 = 0ℚ≠1ℚ
  }

ℚ-Field : Field _ _
ℚ-Field = record { isField = +-*-inv-isField }

_≢?_ : Decidable _≢_
x ≢? y = ¬? (x ≟ y)

-- open HeytingField {!+-*-heytingField!} renaming (Carrier to F) hiding (refl)

-- +-*-decidableField : DecidableField _ _ _
-- +-*-decidableField = record { isDecidableField = record { isHeytingField = {!isHeytingField!} ; decidableInequality = _≢?_ }}
