module Vec.Relation.FirstOrNot where

open import Level
open import Function
open import Data.Bool
open import Data.Product
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Fin
open import Data.Vec as Vec
open import Relation.Nullary

private variable
  ℓ ℓ1 : Level
  A : Set ℓ
  a : A
  b : Bool
  n : ℕ
  P : A → Set ℓ
  xs : Vec A n

data FirstOrNot {A : Set ℓ} (P : A → Set ℓ1) : Vec A n → Bool → Set (ℓ Level.⊔ ℓ1) where
  notHere : FirstOrNot P [] false
  here    : (p : P a) (xs : Vec A n) → FirstOrNot P (a ∷ xs) true
  there   : (¬p : ¬ P a) {xs : Vec A n} (firstOrNot : FirstOrNot P xs b) → FirstOrNot P (a ∷ xs) b

FirstOrNotΣ : {A : Set ℓ} (P : A → Set ℓ1) (xs : Vec A n) → Set (ℓ Level.⊔ ℓ1)
FirstOrNotΣ P xs = Σ Bool $ FirstOrNot P xs

firstOrNotPosition : ∀ {xs : Vec A n} → FirstOrNot P xs true → Fin n
firstOrNotPosition (here p xs) = Fin.zero
firstOrNotPosition (there ¬p xs) = Fin.suc (firstOrNotPosition xs)

firstOrNotPositionMaybe : ∀ {xs : Vec A n} → FirstOrNot P xs b → Maybe $ Fin n
firstOrNotPositionMaybe {b = false} fxs = nothing
firstOrNotPositionMaybe {b = true} fxs = just $ firstOrNotPosition fxs

vReflect : (P : A → Set ℓ) → ℕ → Set _
vReflect P n = Vec (Σ[ x ∈ _ ] Σ[ b ∈ Bool ] Reflects (P x) b) n

boolVec→firstOrNot : (P : A → Set ℓ) (xs : vReflect P n) → FirstOrNotΣ P $ Vec.map proj₁ xs
boolVec→firstOrNot P [] = false , notHere
boolVec→firstOrNot P ((x , false , ofⁿ ¬p) ∷ xs) = _ , there ¬p (boolVec→firstOrNot P xs .proj₂)
boolVec→firstOrNot P ((x , true , ofʸ p) ∷ xs) = true , here p (Vec.map proj₁ xs)

firstOfVReflect : vReflect P n → Maybe $ Fin n
firstOfVReflect [] = nothing
firstOfVReflect ((_ , false , _) ∷ xs) = Maybe.map Fin.suc $ firstOfVReflect xs
firstOfVReflect ((_ , true , _) ∷ xs) = just $ Fin.zero

firstOrNotFromDec : (P? : ∀ a → Dec $ P a) (xs : Vec A n) → FirstOrNotΣ P xs
firstOrNotFromDec P? [] = _ , notHere
firstOrNotFromDec P? (x ∷ xs) with P? x
... | yes p = true , here p xs
... | no ¬p = _ , there ¬p (proj₂ $ firstOrNotFromDec P? xs)

firstTrue : Vec Bool n → Maybe $ Fin n
firstTrue [] = nothing
firstTrue (true ∷ xs) = just $ Fin.zero
firstTrue (false ∷ xs) = Maybe.map Fin.suc (firstTrue xs)
