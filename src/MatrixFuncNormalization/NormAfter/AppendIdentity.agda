open import Level
open import Algebra.Apartness
open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat as ℕ
open import Data.Vec
open import Relation.Binary

open import Algebra.Matrix.Structures
import MatrixFuncNormalization.NormAfter.Base as NormAfter

module MatrixFuncNormalization.NormAfter.AppendIdentity {c} {ℓ₁} {ℓ₂}
  (hField : HeytingField c ℓ₁ ℓ₂)
  (open HeytingField hField renaming (Carrier to F))
  (_≟_ : Decidable _#_) where

  open HeytingCommutativeRing heytingCommutativeRing
  open CommutativeRing commutativeRing
  open MRing rawRing
  open NormAfter hField _≟_

  private variable
    m n p : ℕ


  module _ (xs : Matrix F n m) where

    _++id : Matrix F n (m ℕ.+ n)
    _++id = xs ++ⱽ 1ᴹ

    norm_++id : Matrix F n (m ℕ.+ n)
    norm_++id = normalize _++id

    inverse : Matrix F n n
    inverse = dropⱽ m norm_++id
