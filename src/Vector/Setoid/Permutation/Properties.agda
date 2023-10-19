open import Relation.Binary

module Vector.Setoid.Permutation.Properties {a ℓ} (S : Setoid a ℓ) where

open import Data.Nat
open import Data.Vec.Functional

open import Vector.Base
open import Vector.Setoid.Permutation.Base S

open module S′ = Setoid S renaming (Carrier to A) using (_≈_)

private variable
  m n : ℕ

drop-mid : ∀ {x : A} (ws : Vector A m) xs {ys zs : Vector A n} →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid {zero}  ws xs {ys} {zs} perm = {!!}
drop-mid {suc m} ws xs {ys} {zs} perm = {!!}
