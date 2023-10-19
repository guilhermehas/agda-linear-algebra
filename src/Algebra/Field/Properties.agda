module Algebra.Field.Properties where

open import Level
open import Function
open import Data.Nat hiding (_+_; _*_; _^_; NonZero; nonZero; _⊔_)
open import Data.Integer hiding (_+_; _*_; _^_; NonZero; _⊔_)
open import Data.Product
open import Data.Vec
open import Algebra
open import Algebra.Field.Base
open import Algebra.Ring.Properties as R
open import Algebra.CommRing.Properties as CR
open import Relation.Binary as RB hiding (Decidable)
open import Relation.Unary as RU hiding (Decidable)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

module FieldUnits {ℓ ℓ'} (field' : Field ℓ ℓ') where

  open Field field' renaming (Carrier to A)

  semiRing : RawSemiring _ _
  semiRing = record { Carrier = A ; _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; 0# = 0# ; 1# = 1# }

  open import Algebra.Definitions.RawSemiring semiRing
  open import Relation.Binary.Reasoning.Setoid setoid
  open CR.Units commutativeRing
  open R.Units ring

  private
    A≢0 = Σ[ a ∈ A ] (a ≉ 0#)

    variable
      n : ℕ

  _[_]^_ : (a : A) → (a≉0 : a ≉ 0#) → ℤ → A
  a [ a≉0 ]^ (+ n) = a ^ n
  a [ a≉0 ]^ -[1+ n ] = inv a a≉0 ^ ℕ.suc n

  _^n_ : A≢0 → ℕ → A≢0
  (a , a≉0) ^n n = (a ^ n) , a^n≉0 where
    a^n·a^-n≡1' = ^-presUnit a n (_ , hasInverse a a≉0)

    a^n = a ^ n
    a^-n = a^n·a^-n≡1' .proj₁

    a^n·a^-n≡1 : (a^n * a^-n) ≈ 1#
    a^n·a^-n≡1 = a^n·a^-n≡1' .proj₂


    a^n≉0 : a^n ≉ 0#
    a^n≉0 a^n≡0 = 0≢1 (trans (sym (trans (*-congʳ a^n≡0) (0LeftAnnihilates _))) a^n·a^-n≡1)

  _^z_ : A≢0 → ℤ → A≢0
  a ^z (+ n) = a ^n n
  a@(a' , a≉0) ^z -[1+ n ] = (a⁻¹ , a⁻¹≉0) ^n (ℕ.suc n)  where
    a⁻¹ = inv a' a≉0

    a⁻¹≉0 : a⁻¹ ≉ 0#
    a⁻¹≉0 a⁻¹≡0 = 0≢1 (trans (sym (trans (*-congˡ a⁻¹≡0) (0RightAnnihilates _))) (hasInverse a' a≉0))

  _*n_ : A≢0 → A≢0 → A≢0
  p@(a , a≉0) *n q@(b , b≉0) = (a * b) , a*b≉0 where
    b⁻¹ = inv b b≉0

    b*b⁻¹≡1 = hasInverse b b≉0

    a*b≉0 : (a * b) ≉ 0#
    a*b≉0 a*b≈0 = a≉0 (begin
      a             ≈˘⟨ *-identityʳ _ ⟩
      a * 1#        ≈˘⟨ *-congˡ b*b⁻¹≡1 ⟩
      a * (b * b⁻¹) ≈˘⟨ *-assoc _ _ _ ⟩
      a * b * b⁻¹   ≈⟨ *-congʳ a*b≈0 ⟩
      0# * b⁻¹      ≈⟨ 0LeftAnnihilates _ ⟩
      0# ∎)


  foldr≉0 : (a : A≢0) (xs : Vec A≢0 n) → foldr _ (λ x y → x .proj₁ * y) (a .proj₁) xs ≉ 0#
  foldr≉0 (_ , a≉0) [] = a≉0
  foldr≉0 a (b ∷ xs) = (b *n (_ , foldr≉0 a xs)) .proj₂

  record NonZero (a : A) : Set ℓ' where
    constructor nonZeroC
    field
      nonZero : a ≉ 0#

  mulVec : Vec A≢0 n → A≢0
  mulVec xs = _ , (foldr≉0 (1# , (0≢1 ∘ sym)) xs)

  module DiscA (disc : RB.Decidable _≈_) where

    decP≉0 : (p : A) → Dec (NonZero p)
    decP≉0 p with disc p 0#
    ... | yes p≈0 = no λ where (nonZeroC p≉0) → p≉0 p≈0
    ... | no  p≉0 = yes (nonZeroC p≉0)

    private
      data Decidable {ℓ} {ℓ'} {A : Set ℓ} (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
        isDec : (∀ a → Dec (P a)) → Decidable P

      data AllVec {ℓ} {ℓ'} {A : Set ℓ} (P : A → Set ℓ') : Vec A n → Set (ℓ ⊔ ℓ') where
        emp  : AllVec P []
        consVec : {x : A} (p : P x) {xs : Vec A n} (allXS : AllVec P xs) → AllVec P (x ∷ xs)

      variable
        ℓ'' : Level
        A' B C D : Set ℓ''
        B' B'' : (a : A) → Set ℓ''

      DecAll : Decidable B' → (xs : Vec A n) → Dec (AllVec B' xs)
      DecAll P [] = yes emp
      DecAll P'@(isDec P) (x ∷ xs) with P x | DecAll P' xs
      ... | no ¬p | _ = no (λ where (consVec p allXs) → ¬p p)
      ... | yes p | no ¬q = no (λ where (consVec p allXs) → ¬q allXs)
      ... | yes p | yes q = yes (consVec p q)

    instance
      toDecAll : ⦃ decB : Decidable B' ⦄ {xs : Vec A n} {decVec : True (DecAll decB xs)} → AllVec B' xs
      toDecAll ⦃ decB = decB ⦄ {[]} {decVec} = emp
      toDecAll ⦃ decB = P'@(isDec P) ⦄ {x ∷ xs} {decVec} with P x | DecAll P' xs
      ... | yes x | yes xs = consVec x xs

      DecNonZero : Decidable NonZero
      DecNonZero = isDec decP≉0

    vec→vec≉0 : (xs : Vec A n) ⦃ xs≉0 : AllVec NonZero xs ⦄ → Vec A≢0 n
    vec→vec≉0 [] = []
    vec→vec≉0 (x ∷ xs) ⦃ consVec (nonZeroC nonZero) xs≉0 ⦄ = (x , nonZero) ∷ vec→vec≉0 xs ⦃ xs≉0 ⦄
