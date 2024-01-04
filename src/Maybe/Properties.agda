open import Relation.Binary.Core using (Rel)

module Maybe.Properties
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Data.Maybe.Relation.Binary.Connected using (Connected; nothing; nothing-just; just)
open import Relation.Binary.Construct.Add.Infimum.NonStrict _≤_
open import Relation.Nullary.Construct.Add.Infimum

≤₋-connected : ∀ {k l} → k ≤₋ l → Connected _≤_ k l
≤₋-connected (⊥₋≤ ⊥₋) = nothing
≤₋-connected (⊥₋≤ [ k ]) = nothing-just
≤₋-connected [ p ] = just p
