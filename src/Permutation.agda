open import Level
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

private variable
  a : Level
  A : Set a

rev-perm : (xs : List A) → reverse xs ↭ xs
rev-perm [] = ↭-refl
rev-perm (x ∷ xs) = begin
  reverse (x ∷ xs) ≡⟨ unfold-reverse x xs ⟩
  reverse xs ∷ʳ x ↭˘⟨ ∷↭∷ʳ x (reverse xs) ⟩
  x ∷ reverse xs   ↭⟨ prep x (rev-perm xs) ⟩
  x ∷ xs ∎ where
  open PermutationReasoning
