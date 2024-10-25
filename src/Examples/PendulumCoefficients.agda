-- A example for normalization of a matrix of rational numbers
-- Main example at the end: (TODO explain more)

open import Level using (0ℓ)
open import Data.Nat as ℕ hiding (_/_; _≟_)
import Data.Nat.Properties as ℕ
import Data.Integer as ℤ
open import Data.Fin hiding (_≟_)
open import Data.Product
open import Data.Vec
import Data.Vec.Relation.Binary.Pointwise.Inductive as PI
open import Data.Rational.Unnormalised hiding (truncate)
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_]; setoid)
open import Relation.Unary hiding (Decidable)
open import Relation.Nullary.Decidable
open import Algebra
open import Algebra.Module
import Algebra.Module.Instances.FunctionalVector as AMIF
open import Algebra.Apartness

open import Algebra.SubModule
import Algebra.MatrixData.Relation.Setoid as MSetoid
open import Rational.Unnormalized.Properties
open import Rational.Unnormalized.Literals
import MatrixNormalization.normLinesField as NormField

open HeytingField +-*-heytingField renaming (Carrier to F) hiding (refl)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (ring)
open AMIF ring using (leftModule; _≈ᴹ_)

module Examples.PendulumCoefficients (theoEq : {n : ℕ} {x y : Fin n → ℚᵘ}
      {VS : Cᴹ (leftModule n) 0ℓ} →
      x ≈ᴹ y → x ∈ VS → y ∈ VS) where

private variable
  m n p : ℕ

open MSetoid setoid
open NormField +-*-heytingField _≠?_ theoEq hiding (Matrix) renaming (MatrixData to Matrix)

_≋v_ : Rel (Vec ℚᵘ n) 0ℓ
_≋v_ = PI.Pointwise _≈_

_≟v_ : Decidable (_≋v_ {n})
_≟v_ = PI.decidable _≃?_

_≟_ : Decidable (_≋_ {m} {n})
_≟_ = decidable _≃?_

_+++_ : Matrix m n → Matrix p n → Matrix (m ℕ.+ p) n
[] +++ [] = []
(x ∷ xs) +++ (y ∷ ys) = (x ++ y) ∷ (xs +++ ys)

allZeros : ∀ m n → Matrix m n
allZeros m zero = []
allZeros m (suc n) = replicate _ 0ℚᵘ ∷ allZeros m n

SquareMatrix : ℕ → Set _
SquareMatrix n = Matrix n n

idMat : ∀ n → SquareMatrix n
idMat zero = []
idMat (suc n) = subst SquareMatrix (ℕ.+-comm n 1) matrixRes
  where

  matrixN : Matrix (n ℕ.+ 1) n
  matrixN = idMat n +++ allZeros 1 n

  matrixRes : Matrix (n ℕ.+ 1) (n ℕ.+ 1)
  matrixRes = matrixN ++ [ replicate _ 0ℚᵘ ++ [ 1ℚᵘ ]  ]

matrix22 : Matrix 2 2
matrix22 = (1ℚᵘ ∷ [ 1ℚᵘ ] )
        ∷ [ 1ℚᵘ ∷ [ 2ℚᵘ ] ]

normedMatrix22 : Matrix _ _
normedMatrix22 = normalizeD matrix22

normedMatrix22Res : Matrix 2 2
normedMatrix22Res = (1ℚᵘ ∷ [ 1ℚᵘ ])
                 ∷ [ 0ℚᵘ ∷ [ 1ℚᵘ ] ]

normed22≡res : normedMatrix22 ≋ normedMatrix22Res
normed22≡res = from-yes (normedMatrix22 ≟ normedMatrix22Res)

nCol = 3
nRow = 5

pendulumExample : Matrix nCol nRow
pendulumExample =
  -- L   M      T
  (1ℚᵘ ∷ 0ℚᵘ ∷ -2ℚᵘ ∷ []) ∷ -- acceleration
  (0ℚᵘ ∷ 1ℚᵘ ∷  0ℚᵘ ∷ []) ∷ -- mass
  (1ℚᵘ ∷ 0ℚᵘ ∷  0ℚᵘ ∷ []) ∷ -- time
  (0ℚᵘ ∷ 0ℚᵘ ∷  1ℚᵘ ∷ []) ∷
  (0ℚᵘ ∷ 0ℚᵘ ∷  0ℚᵘ ∷ []) ∷
  []

pendulum++id : Matrix (nCol ℕ.+ nRow) nRow
pendulum++id = pendulumExample +++ idMat _

-- 1 0 -2 | 1 0 0 0 0
-- 0 1  0 | 0 1 0 0 0
-- 1 0  0 | 0 0 1 0 0
-- 0 0  1 | 0 0 0 1 0 line 3
-- 0 0  0 | 0 0 0 0 1

pendulumNormed : Matrix (nCol ℕ.+ nRow) nRow
pendulumNormed = normalizeD pendulum++id

-- 1  0 -2 |
-- 0  2  0 |
-- 0  0  2 |
-- 0  0  0 | line 3 is the first line with all zeros
-- 0  0  0 |

coeff : Vec ℚᵘ nRow
coeff = drop nCol (lookup pendulumNormed (fromℕ<″ 3 (less-than-or-equal refl)))

-- | 0 0 0 | 1 0 -1 2 0

coeffRes : Vec ℚᵘ nRow
coeffRes = 1ℚᵘ ∷ 0ℚᵘ ∷ -1ℚᵘ ∷ 2ℚᵘ ∷ 0ℚᵘ ∷ []

coeff≡coeffRes : coeff ≋v coeffRes
coeff≡coeffRes = from-yes (coeff ≟v coeffRes)

coeff2 : Vec ℚᵘ nRow
coeff2 = drop nCol (lookup pendulumNormed (fromℕ<″ 4 (less-than-or-equal refl)))
