{-# OPTIONS --allow-incomplete-matches #-}

module Examples.Paper where

open import PreludeAlgLin

A = (1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]
b : Vec ℚ _
b = 3 ∷ [ 1 ]

solAb : _
solAb with OneSol {2} v ← solveAllT A b = v

_ : solAb ≡ 2 ∷ [ 1 ]
_ = refl

_ : A *ᴹⱽ solAb ≡ b
_ = refl

sol₂ : _
sol₂ with MultSol {1} s ← solveAllT ([ 1 ∷ [ -1 ] ]) [ 1 ] = s

_ : sol₂ ≡ (1 ∷ [ 0 ]) +span [ 1 ∷ [ 1 ] ]
_ = refl
