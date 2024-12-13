module Examples.NormRational where

open import Function
open import Data.Nat as ℕ hiding (_/_; _≟_)
import Data.Integer as ℤ
open import Data.List using (List)
open import Data.Product
open import Data.Vec renaming (_∷_ to infixr 7 _∷_)
open import Data.Unit hiding (_≟_)
open import Data.Rational.Unnormalised hiding (truncate)
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Algebra
open import Algebra.MatrixData
open import Algebra.Apartness
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import MatrixDataNormalization.NormBef as NormField
import MatrixDataNormalization.Base as NormAll

import Algebra.MatrixData.Relation.Setoid as MSetoid
open import Algebra.DecidableField
open import Rational.Unnormalized.Properties
open import Rational.Literals
open import Rational.Unnormalized.Literals
open import SystemEquations.Data +-*-decidableField

open HeytingField +-*-heytingField renaming (Carrier to F) hiding (refl; -_)
open MSetoid setoid

private variable
  m n p : ℕ

open NormField +-*-decidableField
open NormAll +-*-decidableField

_≟_ : Decidable (_≋_ {m} {n})
_≟_ = decidable _≃?_

matrix22 : Matrix ℚᵘ 2 2
matrix22 = (1 ∷ [ 1 ] )
        ∷ [ 1 ∷ [ 2 ] ]

normedMatrix22 : Matrix ℚᵘ _ _
normedMatrix22 = normalizeBef matrix22

normedMatrix22Res : Matrix ℚᵘ 2 2
normedMatrix22Res = (1 ∷ [ 1 ])
                 ∷ [ 0 ∷ [ 1 ] ]

normed22≡res : normedMatrix22 ≋ normedMatrix22Res
normed22≡res = from-yes (normedMatrix22 ≟ normedMatrix22Res)

normed22Coeff : List _
normed22Coeff = getCoeff matrix22


-- Testing Normalize all the matrix

normedMatrix22End : Matrix ℚᵘ _ _
normedMatrix22End = normalize matrix22

normedMatrix22ResEnd : Matrix ℚᵘ 2 2
normedMatrix22ResEnd = (1 ∷ [ 0 ])
                    ∷ [ 0 ∷ [ 1 ] ]

normed22≡resEnd : normedMatrix22End ≋ normedMatrix22ResEnd
normed22≡resEnd = from-yes (normedMatrix22End ≟ normedMatrix22ResEnd)

coeffs = getCoeff matrix22

-- Testing Solving equations

b : Vec ℚᵘ 2
b = 3 ∷ 5 ∷ []

systemEquations : SystemEquations _ _
systemEquations = system matrix22 b

solution : Solution _
solution = solve systemEquations

_ : sizeSolution solution ≡ 0
_ = refl


{-

A = | 1 1 |
    | 1 2 |

b = | 3 |
    | 5 |

Solve: A*x=b

Solution: is
  x = | 1 |
      | 2 |
if it would be a whole subspace:
  x = v0 + span(v1,v2,...,vk)
    = {v0 + sum a_i v_i | forall a_i ∈ Real}

-- in contrast, the current "VecAffine" is a transpose of that

-}

_ : solSimple solution ≡ 1 ∷ 2 ∷ []
_ = refl


_ : solveComplex [ 1 ∷ [ -2 ] ] [ 3 ] ≡ 3 ∷ [ 0 ] +span [ 2 ∷ [ 1 ] ]
_ = refl


-- Example of the paper: x = -1/2 g*t^2

_ : solveComplex0 ((1 ∷ 0 ∷ [ -2 ]  ) ∷
                  [ 0 ∷ 1 ∷ [  1 ] ]) ≡ [ 2 ∷ -1 ∷ [ 1 ] ]
_ = refl

-- Pendulum Example
-- https://en.wikipedia.org/wiki/Buckingham_%CF%80_theorem#The_simple_pendulum

_ : solveComplex0 ((1 ∷ 0 ∷ 0 ∷ [ -2 ])
                ∷  (0 ∷ 1 ∷ 0 ∷ [  0 ])
                ∷ [ 0 ∷ 0 ∷ 1 ∷ [  1 ] ]) ≡ [ 2 ∷ 0 ∷ -1 ∷ [ 1 ] ]
_ = refl
