module Vec.VecBool.Base where

open import Level using (Level)
open import Function
open import Data.Nat
open import Data.Vec
open import Data.Vec.Relation.Unary.Linked
open import Data.Fin as F using (Fin)
open import Data.Fin.Patterns

private variable
  ℓ : Level
  m n p : ℕ

data VecBool : (m p n : ℕ) → Set where
  []    : VecBool zero zero zero
  consF : VecBool p m n → VecBool (suc p) m (suc n)
  consT : VecBool p m n → VecBool p (suc m) (suc n)

IsNormed : (xs : Vec (Fin n) m) → Set
IsNormed = Linked F._<_

toVBool : {xs : Vec (Fin n) m} (isNormed : IsNormed xs) → VecBool (n ∸ m) m n
toVBool {zero} [] = []
toVBool {suc n} [] = consF (toVBool [])
toVBool {suc n} [-] = consT (toVBool [])
toVBool (_∷_ {n} {xs = F.suc x ∷ xs} x<r isNormed) = {!n!}
