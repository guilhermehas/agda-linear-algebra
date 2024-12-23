module Examples.Paper where

open import PreludeAlgLin

A = (1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]
b : Vec ℚ _
b = 3 ∷ [ 1 ]

solAb = solveAll A b

_ : solAb ≡ 2 ∷ [ 1 ]
_ = refl

_ : A *ᴹⱽ solAb ≡ b
_ = refl

_ : solveAll ([ 1 ∷ [ -1 ] ]) [ 1 ] ≡ (1 ∷ [ 0 ]) +span [ 1 ∷ [ 1 ] ]
_ = refl
