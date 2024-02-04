module Vec.Updates.Reflection where

open import Level
open import Function
open import Data.Empty
open import Data.Bool
open import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Data.Product
open import Data.Nat hiding (less-than-or-equal)
open import Data.Fin as Fin
open import Data.Vec as Vec hiding (_[_]≔_)
import Data.Vec.Properties as Vec
open import Data.Vec.Functional using (Vector; fromVec)
open import Data.Vec.Functional.Properties using (updateAt-updates; updateAt-minimal)
open import Relation.Binary.PropositionalEquality
open import Vec.Relation.FirstOrNot
open import Relation.Nullary.Decidable
open import Relation.Nullary

open import Vector
open import Vec.Updates.Base

private variable
  ℓ : Level
  A : Set ℓ
  a : A
  m n p q : ℕ
  b : Bool
  xs : Vec A n

module VecUpdate where
  FinExpr FinEq  : ℕ → ℕ → Set
  FinExpr m n = Fin n × Vec (Fin n) m
  FinEq m n = FinExpr m n × FinExpr m n

  _⟦_⟧_ : MFin m → FinExpr m n → Vec A n → A
  pos ⟦ a , xs ⟧ ρ = evalFromPosition (Vec.map (fromVec ρ) xs) (lookup ρ a) pos

  _⟦_⟧≡_ : MFin m → FinEq m n → Vec A n → Set _
  pos ⟦ left , right ⟧≡ ρ = pos ⟦ left ⟧ ρ ≡ pos ⟦ right ⟧ ρ

  eval : MFin m → FinExpr m n → Fin n
  eval pos (a , xs) = evalFromPosition xs a pos

  evalEq : ((left , right) : FinEq m n) (pos : MFin m) → Dec (eval pos left ≡ eval pos right)
  evalEq (left , right) pos = eval pos left Fin.≟ eval pos right

  theo-correct : (finEq : FinEq m n) (pos : MFin m) → True (evalEq finEq pos) → (ρ : Vec A n) → pos ⟦ finEq ⟧≡ ρ
  theo-correct ((a , b) , c , right) nothing eqB ρ rewrite toWitness eqB = refl
  theo-correct ((a , b) , c , right) (just i) eqB ρ rewrite Vec.lookup-map i (lookup ρ) b
    | Vec.lookup-map i (lookup ρ) right | toWitness eqB = refl

  findProof : (finEq : FinEq m n) (pos : MFin m) → Maybe $ ∀ (ρ : Vec A n) → pos ⟦ finEq ⟧≡ ρ
  findProof findEq pos with evalEq findEq pos in eq
  ... | no _ = nothing
  ... | yes p = just $ theo-correct findEq pos $ fromWitness p


FinExpr FinEq : (m n p : ℕ) → Set
FinExpr m n p = Fin n × Vec (Fin n) m × Vec (Fin p) m
FinEq m n p = FinExpr m n p × FinExpr m n p

Context : Set ℓ → (n p q : ℕ) → Set ℓ
Context A n p q = Vector A q × Vector (Fin q) n × Vector A p

⟦_⟧v_ : FinExpr m n p → Context A n p q → Vector A q
⟦ i , [] , [] ⟧v (xs , findSub , valuesSub) = xs
⟦ i , ind ∷ indices , val ∷ values ⟧v cont@(xs , findSub , valuesSub) =
 (⟦ i , indices , values ⟧v cont) [ findSub ind ]≔ valuesSub val

⟦_⟧_ : FinExpr m n p → Context A n p q → A
⟦ finExpr@(i , indices , values) ⟧ cont@(xs , finSub , valuesSub) = (⟦ finExpr ⟧v cont) (finSub i)

⟦_⟧≡_ : FinEq m n p → Context A n p q → Set _
⟦ left , right ⟧≡ ρ = ⟦ left ⟧ ρ ≡ ⟦ right ⟧ ρ

evalBool : FinExpr m n p → Vector Bool n → Maybe $ Fin p
evalBool (i , [] , []) vBool = nothing
evalBool (i , ind ∷ indices , val ∷ values) vBool = if vBool ind
  then just val
  else evalBool (i , indices , values) vBool

EvalEquality : (finEq : FinEq m n p) (vBool : Vector Bool n) → Set _
EvalEquality (left , right) vBool = evalBool left vBool ≡ evalBool right vBool

evalBoolEq : (finEq : FinEq m n p) (vBool : Vector Bool n)
  → Dec $ EvalEquality finEq vBool
evalBoolEq (left , right) vBool = ≡-dec Fin._≟_ _ _
