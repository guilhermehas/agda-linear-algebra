module Algebra.MatrixData.Structures where

open import Level using (Level; _⊔_)
open import Function
open import Algebra
open import Data.Product using (_,_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec
open import Data.Vec.Relation.Unary.All as VAll using (All)
import Algebra.MatrixData.Base as MBase
open import Relation.Binary
open import Relation.Nullary

open import Algebra.BigOpsData

private variable
  a ℓ : Level
  B : Set ℓ
  m n p k : ℕ

module MAddition  (_+_ : Op₂ B) where
  infixl 6 _+ᴹ_

  open MBase public

  _+ᴹ_ : Op₂ (Matrix B m n)
  _+ᴹ_ = zipWith $ zipWith _+_

module MMonoid (rawMonoid : RawMonoid a ℓ) where
  infix  4 _≈ᴹ_

  open RawMonoid rawMonoid renaming (Carrier to A)
  open MAddition _∙_ public
  open SumRawMonoid rawMonoid

  0ᴹ : Matrix A m n
  0ᴹ = replicate _ (replicate _ ε)

  _≈ᴹ_ : Rel (Matrix A m n) _
  M ≈ᴹ N = All (λ (xs , ys) → All (λ (x , y) → x ≈ y) (zip xs ys)) (zip M N)


module MRing {a} {ℓ} (rawRing : RawRing a ℓ) where
  infixl 7 _*ᴹ_

  open RawRing rawRing renaming (Carrier to A)
  open SumRawRing rawRing public
  open MMonoid +-rawMonoid public

  private variable
    xs xs‵ ys zs : Matrix A m n

  private
    add0ₗ : Matrix A n m → Matrix A n (suc m)
    add0ₗ [] = []
    add0ₗ (x ∷ xs) = (0# ∷ x) ∷ add0ₗ xs

  1ᴹ : Matrix A n n
  1ᴹ {zero} = []
  1ᴹ {suc n} = (1# ∷ replicate _ 0#) ∷ (add0ₗ 1ᴹ)

  _*ᴹ_ : Matrix A n m → Matrix A m p → Matrix A n p
  _*ᴹ_ {n} {m} {p} M N = map (λ row → map (λ column → ∑ (zipWith _*_ row column)) (transpose N)) M

  _*ᴹⱽ_ : ∀ {m n} → Matrix A n m → Vec A _ → Vec A n
  A *ᴹⱽ x = m→v (A *ᴹ transpose [ x ])
