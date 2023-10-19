open import Relation.Binary

module MatrixFuncNormalization.MatrixPropsAfter {c ℓ₁ ℓ₂} (totalOrder : StrictTotalOrder c ℓ₁ ℓ₂) where

open import Level using (Level; _⊔_; Lift; lower; lift)
open import Function
open import Data.Unit
open import Data.Bool using (true; false)
open import Data.Product
open import Data.Nat using (ℕ; z≤n; s≤s; suc)
open import Data.Nat.Properties as ℕ hiding (<⇒≢; _≤?_; _≟_; ≤∧≢⇒<; <-asym; <-trans)
open import Data.Fin.Base as F using (Fin; zero; suc; inject₁; fromℕ)
open import Data.Fin.Properties hiding (≤-refl; <-trans)
open import Data.Sum as Π
open import Data.Vec.Functional
open import Relation.Nullary.Construct.Add.Infimum
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; refl; sym)
import Relation.Binary.Construct.Add.Infimum.Strict as AddInfMod
import Relation.Binary.Construct.Add.Point.Equality as Equality
import Relation.Binary.Construct.StrictToNonStrict as StrictToNonStrict
open import Relation.Unary.Consequences
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Algebra

open import MatrixNormalization.FinProps
open import lbry

module A′ = StrictTotalOrder totalOrder
open AddInfMod A′._<_

private variable
  n : ℕ

<₋-totalOrder : StrictTotalOrder _ _ _
<₋-totalOrder = record { isStrictTotalOrder = <₋-isStrictTotalOrder A′.isStrictTotalOrder }

open module STO = StrictTotalOrder <₋-totalOrder renaming (Carrier to A) hiding (_≟_; _>_)
open module ≈ = IsEquivalence STO.isEquivalence hiding (sym)
open StrictToNonStrict _≈_ _<_
open Equality _≈_ renaming (≈∙-refl to ≈∙-refl′)
open FinProps

_>_ = flip _<_

_<′_ : Rel A _
x <′ y = (x ≈ ⊥₋ × y ≈ ⊥₋) ⊎ x < y
_>′_ = flip _<′_

AllRowsNormalizedRight : Vector A n → Set _
AllRowsNormalizedRight xs = ∀ i j → i F.< j → xs i <′ xs j

simpleFinProps : FinProps (Vector A (ℕ.suc n)) n
Pij simpleFinProps i j i≤j a = ⊤
Pi simpleFinProps i a = ⊤
P simpleFinProps a = ⊤
Pab simpleFinProps i j i≢j a b = ⊤
Pij→Pi simpleFinProps i a pij = _
Pi→P simpleFinProps a pi = _
Pi→Pii simpleFinProps i a pi = _
Ps simpleFinProps i j i≤j a b pij pab = _
P00 simpleFinProps a = _

-- finProps : FinProps (Vector A (suc n)) n
-- Pij finProps = {!!}
-- Pi finProps = {!!}
-- P finProps = {!!}
-- Pab finProps = {!!}
-- Pij→Pi finProps = {!!}
-- Pi→P finProps = {!!}
-- Pi→Pii finProps = {!!}
-- Ps finProps = {!!}
-- P00 finProps = {!!}
