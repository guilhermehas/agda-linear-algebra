open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Apartness
import Relation.Binary.Reasoning.Setoid as ReasonSetoid
open import Data.Product

module Algebra.HeytingField.Properties
  {c ℓ₁ ℓ₂} (HF : HeytingField c ℓ₁ ℓ₂) where

open HeytingField HF
open HeytingCommutativeRing heytingCommutativeRing
open CommutativeRing commutativeRing
open import Algebra.HeytingCommutativeRing.Properties heytingCommutativeRing public
