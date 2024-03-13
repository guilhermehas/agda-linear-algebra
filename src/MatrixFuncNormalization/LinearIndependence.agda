open import Algebra.DecidableField

module MatrixFuncNormalization.LinearIndependence {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra.Matrix
open import Function using (_$_; _∘_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂)
open import Data.Maybe using (is-just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin; fromℕ)

import MatrixFuncNormalization.NormAfter as NormAfter

open DecidableField dField renaming (Carrier to F)
open NormAfter dField

private variable
  m n : ℕ

isLinearIndependentNormed : Matrix F n m → Bool
isLinearIndependentNormed {zero}  xs = true
isLinearIndependentNormed {suc n} xs = is-just $ proj₁ $ findPivAndValue $ xs $ fromℕ _

isLinearDependentNormed : Matrix F n m → Bool
isLinearDependentNormed = not ∘ isLinearIndependentNormed

isLinearIndependent : Matrix F n m → Bool
isLinearIndependent = isLinearIndependentNormed ∘ normalize

isLinearDependent : Matrix F n m → Bool
isLinearDependent = not ∘ isLinearIndependent
