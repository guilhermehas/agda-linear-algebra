open import Level using (Level; levelOfType)
open import Algebra
open import Function
open import Data.Bool using (Bool; if_then_else_; T)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (Σ-syntax; -,_; _,_)
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Binary
open import Relation.Nullary
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as ≋-props

module Vector.Base where

private variable
  c ℓ : Level
  A : Set ℓ
  m n : ℕ
  xs ys zs : Vector A n

infixl 6 _[_]≔_

_[_]≔_ : Vector A n → Fin n → A → Vector A n
xs [ i ]≔ x = updateAt xs i (const x)

swapV : Vector A n → (i j : Fin n) → Vector A n
swapV xs i j = xs [ i ]≔ xs j [ j ]≔ xs i

[_] : A → Vector A 1
[ x ] _ = x

ListVec : Set ℓ → Set _
ListVec A = Σ[ n ∈ ℕ ] Vector A n

filter : (A → Bool) → Vector A n → ListVec A
filter {n = ℕ.zero} f xs = -, []
filter {n = ℕ.suc n} f xs = let x = xs 0F ; _ , fxs = filter f (tail xs) in
  if f x then -, x ∷ fxs else -, fxs

module SetoidProps (S : Setoid c ℓ) where
  open module ≈ = Setoid S
  open ≋-props S

  private variable
    x y : Carrier
    xs‵ ys‵ : Vector Carrier n

  ≋-cons : x ≈ y → xs‵ ≋ ys‵ → (x ∷ xs‵) ≋ (y ∷ ys‵)
  ≋-cons x≈y xs≋ys zero = x≈y
  ≋-cons x≈y xs≋ys (suc i) = xs≋ys i

  ≋-consˡ : xs‵ ≋ ys‵ → (x ∷ xs‵) ≋ (x ∷ ys‵)
  ≋-consˡ = ≋-cons ≈.refl

Monotone : Vector (Fin m) n → Set _
Monotone xs = xs Preserves _<_ ⟶ _<_

findFirst : Vector A n → (A → Bool) → Maybe (Fin n × A)
findFirst {n = ℕ.zero} xs f = nothing
findFirst {n = ℕ.suc n} xs f = if f (xs zero) then just (zero , (xs zero))
  else Maybe.map (λ (i , a) → suc i , a) (findFirst (tail xs) f)

findFirstElement : Vector A n → (A → Bool) → Maybe A
findFirstElement = Maybe.map proj₂ ∘₂ findFirst
