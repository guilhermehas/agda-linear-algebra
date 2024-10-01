open import Level
open import Algebra.Apartness
open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat as ℕ
open import Data.Vec
open import Relation.Binary

open import Algebra.Matrix.Structures
open import Algebra.DecidableField
import MatrixFuncNormalization.NormAfter.Base as NormAfter
import MatrixFuncNormalization.ElimZeros.Base as EZeros

module MatrixFuncNormalization.NormAfter.AppendIdentity {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

  open DecidableField dField renaming (Carrier to F; heytingField to hField)
  open CommutativeRing commutativeRing
  open MRing rawRing
  open NormAfter dField
  open EZeros dField

  private variable
    m n p : ℕ


  module _ (xs : Matrix F n m) where

    _++id : Matrix F n (m ℕ.+ n)
    _++id = xs ++ⱽ 1ᴹ

    norm_++id : Matrix F n (m ℕ.+ n)
    norm_++id = normalize _++id

    inverseWithCoeff : Matrix F n n
    inverseWithCoeff = dropⱽ m norm_++id

    inverse : Matrix F n n
    inverse = dropⱽ m (divideByCoeff norm_++id)
