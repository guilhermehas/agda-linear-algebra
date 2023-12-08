module Examples.NormRational where

open import Data.Nat as ℕ hiding (_/_; _≟_)
import Data.Integer as ℤ
open import Data.List using (List)
open import Data.Vec
import Data.Vec.Relation.Binary.Pointwise.Inductive as PI
import Data.Vec.Relation.Binary.Equality.Setoid as ≈
open import Data.Rational.Unnormalised hiding (truncate)
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Algebra
open import Algebra.MatrixData
open import Algebra.Apartness
import MatrixFuncNormalization.normBef as NormField
import MatrixFuncNormalization.NormAfter as NormAll
import Algebra.MatrixData.Relation.Setoid as MSetoid
open import Rational.Properties

open HeytingField +-*-heytingField renaming (Carrier to F) hiding (refl)
open ≈ setoid renaming (_≋_ to _≋v_)
open MSetoid setoid

private variable
  m n p : ℕ

open NormField +-*-heytingField _≠?_ renaming (normalizeData to normalizeDataBef)
open NormAll +-*-heytingField _≠?_

_≟_ : Decidable (_≋_ {m} {n})
_≟_ = decidable _≃?_

2ℚᵘ : ℚᵘ
2ℚᵘ = ℤ.+ 2 / 1

-1ℚᵘ : ℚᵘ
-1ℚᵘ = (ℤ.- (ℤ.+ 1)) / 1

-2ℚᵘ : ℚᵘ
-2ℚᵘ = (ℤ.- (ℤ.+ 2)) / 1

matrix22 : Matrix ℚᵘ 2 2
matrix22 = (1ℚᵘ ∷ [ 1ℚᵘ ] )
        ∷ [ 1ℚᵘ ∷ [ 2ℚᵘ ] ]

normedMatrix22 : Matrix ℚᵘ _ _
normedMatrix22 = normalizeDataBef matrix22

normedMatrix22Res : Matrix ℚᵘ 2 2
normedMatrix22Res = (1ℚᵘ ∷ [ 1ℚᵘ ])
                 ∷ [ 0ℚᵘ ∷ [ 1ℚᵘ ] ]

normed22≡res : normedMatrix22 ≋ normedMatrix22Res
normed22≡res = from-yes (normedMatrix22 ≟ normedMatrix22Res)

normed22Coeff : List _
normed22Coeff = getCoeff matrix22


-- Testing Normalize all the matrix

normedMatrix22End : Matrix ℚᵘ _ _
normedMatrix22End = normalizeData matrix22

normedMatrix22ResEnd : Matrix ℚᵘ 2 2
normedMatrix22ResEnd = (1ℚᵘ ∷ [ 0ℚᵘ ])
                    ∷ [ 0ℚᵘ ∷ [ 1ℚᵘ ] ]

normed22≡resEnd : normedMatrix22End ≋ normedMatrix22ResEnd
normed22≡resEnd = from-yes (normedMatrix22End ≟ normedMatrix22ResEnd)

coeffs = getCoeff matrix22
