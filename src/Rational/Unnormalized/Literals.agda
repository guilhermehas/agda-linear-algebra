module Rational.Unnormalized.Literals where

open import Agda.Builtin.FromNat using (Number; fromNat) public
open import Agda.Builtin.FromNeg
open import Data.Unit using (⊤)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Literals as ℕ
open import Data.Integer using (ℤ; +_)
import Data.Integer.Literals as ℤ
open import Data.Rational.Unnormalised using (ℚᵘ; -_; _/_)

number : Number ℚᵘ
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → + n / suc zero
  }

negative : Negative ℚᵘ
negative = record
  { Constraint = λ _ → ⊤
  ; fromNeg    = λ n → - ( (+ n) / suc zero)
  }

instance
  NatNumber = ℕ.number
  IntNumber = ℤ.number
  RatNumber = number
  RatNegative = negative

1/1000ℚ = 1 / 1000
2/1000ℚ = 2 / 1000
1/1000000ℚ = 1 / 1000000
2/3000000ℚ = 2 / 3000000

-2ℚ 2ℚ 3ℚ 5ℚ 10ℚ 20ℚ 1000ℚ 2000ℚ 3000ℚ 1000000ℚ 2000000ℚ 3000000ℚ : ℚᵘ
-2ℚ = -2
-1ℚ = -1
2ℚ = 2
3ℚ = 3
5ℚ = 5
10ℚ = 10
20ℚ = 20
1000ℚ = 1000
2000ℚ = 2000
3000ℚ = 3000
1000000ℚ = 1000000
2000000ℚ = 2000000
3000000ℚ = 3000000
