module Algebra.DecidableField.Base where

open import Level using (_⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Apartness.Structures
open import Algebra.Apartness.Bundles
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary
open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Data.Maybe
open import Data.Product

module _
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  where

  record IsDecidableField : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      isHeytingField      : IsHeytingField _≈_ _#_ _+_ _*_ -_ 0# 1#
      decidableInequality : Decidable _#_

    _≟_ = decidableInequality

    open IsHeytingField isHeytingField public

record DecidableField c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _#_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ₁
    _#_              : Rel Carrier ℓ₂
    _+_              : Op₂ Carrier
    _*_              : Op₂ Carrier
    -_               : Op₁ Carrier
    0#               : Carrier
    1#               : Carrier
    isDecidableField : IsDecidableField _≈_ _#_ _+_ _*_ -_ 0# 1#

  open IsDecidableField isDecidableField public

  heytingField : HeytingField c ℓ₁ ℓ₂
  heytingField = record { isHeytingField = isHeytingField }

  open HeytingField heytingField using (heytingCommutativeRing) public
  open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing) public

  almostCommutativeRing : AlmostCommutativeRing _ _
  almostCommutativeRing = fromCommutativeRing commutativeRing ≟?
    where
    ≟? : (x : Carrier) → Maybe (0# ≈ x)
    ≟? x with 0# ≟ x
    ... | yes _ = nothing
    ... | no 0#x = just (tight _ _ .proj₁ 0#x)
