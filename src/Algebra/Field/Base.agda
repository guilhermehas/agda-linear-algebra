module Algebra.Field.Base where

open import Level
open import Function
open import Relation.Binary
open import Relation.Nullary as N
open import Algebra

record IsField {ℓ ℓ'}
  {Carrier : Set ℓ}
  (_≈_     : Rel Carrier ℓ')
  (0# 1# : Carrier)
  (-_ : Op₁ Carrier)
  (_+_ _*_ : Op₂ Carrier)
  (inv : (p : Carrier) (p≠0 : ¬ (p ≈ 0#)) → Carrier)
  : Set (ℓ ⊔ ℓ') where

  infix 4 _≉_
  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

  field
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
    hasInverse        : (x : Carrier) (x≭0 : ¬ x ≈ 0#) → (x * inv x x≭0) ≈ 1#
    0≢1               : 0# ≉ 1#

  open IsCommutativeRing isCommutativeRing public

  div : (p q : Carrier) → q ≉ 0# → Carrier
  div p q q≉0 = p * inv q q≉0

record Field ℓ ℓ' : Set (suc (ℓ ⊔ ℓ')) where
  constructor fieldc
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_

  field
    Carrier : Set ℓ
    _≈_     : Rel Carrier ℓ'
    0# 1# : Carrier
    -_ : Op₁ Carrier
    _+_ _*_ : Op₂ Carrier
    inv : (p : Carrier) (p≠0 : ¬ (p ≈ 0#)) → Carrier
    isField : IsField _≈_ 0# 1# -_ _+_ _*_ inv

  open IsField isField public

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  open CommutativeRing commutativeRing public using (
      commutativeSemiring ; ring
    ; +-rawMagma; +-magma; +-unitalMagma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; *-rawMagma; *-magma; *-commutativeMagma; *-semigroup; *-commutativeSemigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne
    )
