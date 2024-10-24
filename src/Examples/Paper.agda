module Examples.Paper where

open import Data.Unit using ()
open import Rational.Literals
open import Data.Vec
open import Data.Rational.Unnormalised using (_/_)
open import Rational.Properties using (+-*-decidableField)
open import SystemEquations.Data +-*-decidableField
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

_ : solveComplex ((1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]) (3 ∷ [ 1 ]) ≡ (8 / 4 ∷ [ 2 / 2 ]) +span []
_ = refl
