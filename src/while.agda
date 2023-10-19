open import Relation.Nullary.Negation.Core using (¬_)
open import Data.Product
open import Data.Sum
open import Level using (Level)
open import Function
open import Induction.WellFounded
open import Relation.Unary using (Pred)
open import Relation.Binary

module while  {ℓ ℓ₁ ℓ₂ ℓ₃} (State : Set ℓ) (_<_ : Rel State ℓ₁) (wellFounded : WellFounded _<_)
  (P : Pred State ℓ₂) (inLoop : Pred State ℓ₃)
  (step : State → State) (stepState : ∀ {state} → P state × inLoop state → P (step state))
  (step< : ∀ state → ¬ inLoop state ⊎ inLoop state × step state < state)
  where

recursion : (state : State) → P state → Σ[ st ∈ State ] P st × ¬ (inLoop st)
recursion state Pst = induct Pst (step< state) (wellFounded state) where
  induct : ∀ {j} → P j → ¬ (inLoop j) ⊎ inLoop j × step j < j → Acc _<_ j
    → Σ[ st ∈ State ] (P st × ¬ (inLoop st))
  induct {j} Pj (inj₁ isFinal) (acc rs) = j , Pj , isFinal
  induct {j} Pj (inj₂ (inLoop , pStep)) (acc rs) =
    induct {step j} (stepState (Pj , inLoop)) (step< (step j)) (rs _ pStep)
