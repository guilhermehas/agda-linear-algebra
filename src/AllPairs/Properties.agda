open import Relation.Binary using (Rel)

module AllPairs.Properties {ℓ} {A : Set ℓ} (_∼_ : Rel A ℓ) where

open import Function
open import Data.Maybe
open import Data.Maybe.Relation.Binary.Pointwise
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs as AP

_≈_ = Pointwise _∼_

pointwise⁺All : ∀ {x} {xs : List (Maybe A)} → All (just x ≈_) xs → All (x ∼_) (catMaybes xs)
pointwise⁺All {xs = []} _ = []
pointwise⁺All {xs = just _ ∷ _} (just px ∷ ys) = px ∷ pointwise⁺All ys

pointwise⁺ : {xs : List (Maybe A)} → AllPairs _≈_ xs → AllPairs _∼_ (catMaybes xs)
pointwise⁺ {xs = []} _ = []
pointwise⁺ {xs = nothing ∷ _} (x∼ys ∷ allYs) = pointwise⁺ allYs
pointwise⁺ {xs = just  _ ∷ _} (x∼ys ∷ allYs) = pointwise⁺All x∼ys AP.∷ pointwise⁺ allYs
