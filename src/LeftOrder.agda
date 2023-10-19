open import Data.Sum.Base as Sum
open import Data.Sum.Relation.Binary.Pointwise as PW
  using (Pointwise; inj₁; inj₂)
open import Data.Product
open import Data.Empty
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Sum.Relation.Binary.LeftOrder hiding (⊎-<-strictTotalOrder)

module _ {a b c d e f} where

  ⊎-<-strictTotalOrder : StrictTotalOrder a b c →
                         StrictTotalOrder d e f →
                         StrictTotalOrder _ _ _
  ⊎-<-strictTotalOrder sto₁ sto₂ = record
    { isStrictTotalOrder = ⊎-<-isStrictTotalOrder (isStrictTotalOrder sto₁) (isStrictTotalOrder sto₂)
    } where open StrictTotalOrder
