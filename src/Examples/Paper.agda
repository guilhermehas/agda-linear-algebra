module Examples.Paper where

open import Data.Unit using ()
open import Data.Vec
open import Rational.Literals
open import Rational.Properties using (+-*-decidableField)
open import SystemEquations.Data +-*-decidableField
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

_ : solveSimple ((1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]) (3 ∷ [ 1 ]) ≡ 2 ∷ [ 1 ]
_ = refl
