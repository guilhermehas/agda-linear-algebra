module PreludeAlgLin where

open import Algebra
open import Data.Unit using (tt) public
open import Data.Nat using (ℕ) public
open import Data.Vec hiding (truncate) public
open import Data.Rational using (ℚ) public
open import Rational.Literals public
open import Rational.Properties using (+-*-decidableField) public
open import Data.Rational.Properties using (+-*-ring)
open import SystemEquations.Data +-*-decidableField public
open import Relation.Binary.PropositionalEquality using (refl; _≡_) public

open import Algebra.MatrixData.Structures

module MR = MRing (Ring.rawRing +-*-ring)
open MR public hiding (Matrix)

Matrix : (n m : ℕ) → Set
Matrix n m = MR.Matrix ℚ n m
