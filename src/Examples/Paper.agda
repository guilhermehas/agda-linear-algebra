module Examples.Paper where

-- TODO: Add LinAlgPrelude
-- TODO: Add multiply/add matrix
open import Data.Unit using ()
open import Data.Vec
open import Data.Rational using (ℚ)
open import Rational.Literals
open import Rational.Properties using (+-*-decidableField)
open import SystemEquations.Data +-*-decidableField
open import Relation.Binary.PropositionalEquality using (refl; _≡_)


A = (1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]
b : Vec ℚ _
b = 3 ∷ [ 1 ]

solAb = solveSimple A b

_ : solAb ≡ 2 ∷ [ 1 ]
_ = refl

-- _ : {!A * solAb!} ≡ b
-- _ = refl 

_ : solveComplex ([ 1 ∷ [ -1 ] ]) [ 1 ] ≡ (1 ∷ [ 0 ]) +span [ 1 ∷ [ 1 ] ]
_ = refl