module Vec.VecBool.Base where

open import Level using (Level)
open import Function
open import Data.Nat
open import Data.Vec
open import Data.Product
open import Data.Vec.Relation.Unary.Linked as L hiding (head)
open import Data.Fin as F using (Fin)
open import Data.Fin.Properties
open import Data.Fin.Patterns

private variable
  ℓ : Level
  m n p : ℕ

data VecBool : (m n : ℕ) → Set where
  []    : VecBool zero zero
  consF : VecBool m n → VecBool m (suc n)
  consT : VecBool m n → VecBool (suc m) (suc n)

IsNormed : (xs : Vec (Fin n) m) → Set
IsNormed = Linked F._<_

tailIsNormed′ : {xs : Vec (Fin (ℕ.suc n)) (suc m)} (0<xs : F.zero {suc m} F.< head xs) (isNormed : IsNormed xs)
  → (Vec (Fin n) (suc m))
tailIsNormed′ {m = zero} {xs = F.suc x ∷ xs} 0<xs isNormed = [ x ]
tailIsNormed′ {m = suc m} {xs = F.suc x ∷ xs} 0<xs (x<r ∷ isNormed) = x ∷ tailIsNormed′ (<-trans 0<xs x<r) isNormed

tailIsNormed : {xs : Vec (Fin (ℕ.suc n)) (suc m)} (0<xs : F.zero {suc m} F.< head xs) (isNormed : IsNormed xs)
  → Σ (Vec (Fin n) (suc m)) IsNormed
proj₁ (tailIsNormed 0<xs isNormed) = tailIsNormed′ 0<xs isNormed
proj₂ (tailIsNormed {m = zero} {F.suc x ∷ xs} 0<xs isNormed) = [-]
proj₂ (tailIsNormed {m = suc m} {F.suc x ∷ xs} 0<xs (x<r ∷ isNormed)) =
  help 0<xs x<r isNormed ∷ proj₂ (tailIsNormed (<-trans 0<xs x<r) isNormed)
  where
  help : ∀ {m} {xs} {x} (0<xs : (F.zero {m}) F.< F.suc x) (x<r  : F.suc x F.< head xs)
    (isNormed : Linked F._<_ xs)
    → x F.< head (tailIsNormed′ {m = m} {xs = xs} (<-trans 0<xs x<r) isNormed)
  help {zero} {F.suc y ∷ xs} {x} _ (s≤s x<r) isNormed = x<r
  help {suc m} {F.suc y ∷ xs} {x} _ (s≤s x<r) (_ ∷ isNormed) = x<r

isNormedPred′ : ∀ {xs : Vec (Fin (ℕ.suc n)) (suc m)} {x : Fin n} (isNormed : IsNormed (F.suc x ∷ xs))
  → Vec (Fin n) (suc m)
isNormedPred′ {m = zero} {xs = F.suc y ∷ xs} {x} (x<r ∷ isNormed) = [ y ]
isNormedPred′ {m = suc m} {xs = F.suc y ∷ xs} {x} (x<r ∷ isNormed) = y ∷ isNormedPred′ isNormed

isNormedPred : ∀ {xs : Vec (Fin (ℕ.suc n)) (suc m)} {x : Fin n} (isNormed : IsNormed (F.suc x ∷ xs))
  → Σ[ ys ∈ (Vec (Fin n) (suc m)) ] IsNormed (x ∷ ys)
proj₁ (isNormedPred isNormed) = isNormedPred′ isNormed
proj₂ (isNormedPred {m = zero} {F.suc y ∷ xs} {x} (s≤s x<r ∷ isNormed)) = x<r ∷ [-]
proj₂ (isNormedPred {m = suc m} {F.suc y ∷ xs} {x} (s≤s x<r ∷ isNormed)) = x<r ∷ proj₂ (isNormedPred isNormed)

toVBool : {xs : Vec (Fin n) m} (isNormed : IsNormed xs) → VecBool m n
toVBool {zero} {xs = []} [] = []
toVBool {suc n} {xs = []} [] = consF (toVBool [])
toVBool {suc n} {xs = x ∷ _} [-] = consT (toVBool [])
toVBool {suc n} {xs = 0F ∷ xs} (x<ys ∷ linked) = consT (toVBool (proj₂ (tailIsNormed x<ys linked)))
toVBool {2+ n} {xs = F.suc x ∷ xs} normed@(_∷_ {m} x<ys linked) =
  consF (toVBool (isNormedPred normed .proj₂))
