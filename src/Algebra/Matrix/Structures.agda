module Algebra.Matrix.Structures where

open import Level using (Level; _⊔_)
open import Function
open import Algebra
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.List
import Algebra.Matrix.Base as MBase
open import Relation.Binary
open import Relation.Nullary

open import Algebra.BigOps

private variable
  a ℓ : Level
  B : Set ℓ
  m n p k : ℕ

module MAddition  (_+_ : Op₂ B) where
  infixl 6 _+ᴹ_

  open MBase public

  _+ᴹ_ : Op₂ (Matrix B m n)
  (xs +ᴹ ys) i j = xs i j + ys i j

module MMonoid (rawMonoid : RawMonoid a ℓ) where
  infix  4 _≈ᴹ_

  open RawMonoid rawMonoid renaming (Carrier to A)
  open MAddition _∙_ public
  open SumMonoid rawMonoid

  0ᴹ : Matrix A m n
  0ᴹ _ _ = ε

  _≈ᴹ_ : Rel (Matrix A m n) _
  M ≈ᴹ N = ∀ i j → M i j ≈ N i j


module MRing {a} {ℓ} (rawRing : RawRing a ℓ) where
  infixl 7 _*ᴹ_
  infixl 5 _▹_

  open RawRing rawRing renaming (Carrier to A)
  open SumRawRing rawRing public
  open MMonoid +-rawMonoid public

  private variable
    xs xs‵ ys zs : Matrix A m n

  1ᴹ : Matrix A n n
  1ᴹ = δ

  _*ᴹ_ : Matrix A m n → Matrix A n p → Matrix A m p
  (M *ᴹ N) i k = ∑ λ j → M i j * N j k

  record IsLinear (T : Matrix A m n → Matrix A k n) : Set (a ⊔ ℓ) where
    field
      transMat : (M : Matrix A m n) → Matrix A k m
      transEq  : (M : Matrix A m n) → T M ≈ᴹ transMat M *ᴹ M

  record MatFunAreLinear
    (transMat : (M : Matrix A m n) → Matrix A k m)
    (T : Matrix A m n → Matrix A k n) : Set (a ⊔ ℓ) where

    field
      transEq  : (M : Matrix A m n) → T M ≈ᴹ transMat M *ᴹ M

  swapMatrix : (p q : Fin n) → Matrix A n n
  swapMatrix p q i j with p ≟ i | q ≟ i
  ... | yes _ | _ = δ q j
  ... | _ | yes _ = δ p j
  ... | _ |     _ = δ i j

  _[_]≔_*[_] : Matrix A m n → Fin m → A → Fin m → Matrix A m n
  (M [ p ]≔ r *[ q ]) i j with q ≟ i
  ... | yes _ = M i j + r * M p j
  ... | no  _ = M i j

  addConstRowMatrix : (p q : Fin n) (r : A) → Matrix A n n
  addConstRowMatrix p q r i j with q ≟ i
  ... | yes _ = δ i j + r * δ p j
  ... | no  _ = δ i j

  data MatrixOps (m n : ℕ) : Set a where
    swapOp  : (p q : Fin m)         → MatrixOps m n
    addCons : (p q : Fin m) (r : A) → MatrixOps m n

  matOps→mat : MatrixOps m n → Matrix A m m
  matOps→mat (swapOp p q)    = swapMatrix p q
  matOps→mat (addCons p q r) = addConstRowMatrix p q r

  matOps→func : MatrixOps m n → Matrix A m n → Matrix A m n
  matOps→func (swapOp p q)       = swap p q
  matOps→func (addCons p q r) xs = xs [ p ]≔ r *[ q ]

  listMatOps→mat : List (MatrixOps m n) → Matrix A m m
  listMatOps→mat = foldr (_*ᴹ_ ∘ matOps→mat) 1ᴹ

  listMatOps→func : List (MatrixOps m n) → Op₁ (Matrix A m n)
  listMatOps→func = foldr (λ mops → (matOps→func mops) ∘_) id

  data _▹_ : Rel (Matrix A m n) (a ⊔ ℓ) where
    idR : xs ≈ᴹ ys → xs ▹ ys
    rec : (mOps : MatrixOps m n)
      → xs ▹ ys
      → matOps→func mOps ys ≈ᴹ zs
      → xs ▹ zs
    -- transR : xs ▹ ys → ys ▹ zs → xs ▹ zs

  ▹⇒listMops : {xs : Matrix A m n} → xs ▹ ys → List (MatrixOps m n)
  ▹⇒listMops (idR _) = []
  ▹⇒listMops (rec mOps xs▹ys _) = mOps ∷ ▹⇒listMops xs▹ys
  -- ▹⇒listMops (transR xs▹ys ys▹zs) = ▹⇒listMops xs▹ys ++ ▹⇒listMops ys▹zs
