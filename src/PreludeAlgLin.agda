module PreludeAlgLin where


open import Data.Unit using () public
open import Data.Nat using (ℕ) public
open import Data.Vec hiding (truncate) public
open import Data.Rational public
open import Rational.Literals public
open import Rational.Properties using (+-*-decidableField) public
open import Data.Rational.Properties using (+-*-ring)
open import SystemEquations.Data +-*-decidableField public
open import Relation.Binary.PropositionalEquality using (refl; _≡_) public

import Algebra.MatrixData.Base as MB
open MB hiding (Matrix) public

open import Algebra.BigOpsData
open SumRing +-*-ring public


Matrix : (n m : ℕ) → Set
Matrix n m = MB.Matrix ℚ n m
