module Examples.Paper where

open import PreludeAlgLin

A = (1 ∷ [ 1 ]) ∷ [ 1 ∷ [ -1 ] ]
b : Vec ℚ _
b = 3 ∷ [ 1 ]

solAb = solveSimple A b

_ : solAb ≡ 2 ∷ [ 1 ]
_ = refl

m→v : ∀ {n} → Matrix n 1 → Vec ℚ n
m→v [] = {!!}
m→v (A₁ ∷ A₂) = {!!}

_*ᴹⱽ_ : ∀ {m n} → Matrix n m → Vec ℚ _ → Vec ℚ n
A *ᴹⱽ x = m→v (A *ᴹ transpose [ x ])

_ : A *ᴹ transpose [ solAb ] ≡ transpose [ b ]
_ = refl

_ : A *ᴹⱽ solAb ≡ b
_ = refl

-- TODO: create *ᴹⱽ
-- _ : A *ᴹⱽ solAb ≡ b
-- _ = refl

_ : solveComplex ([ 1 ∷ [ -1 ] ]) [ 1 ] ≡ (1 ∷ [ 0 ]) +span [ 1 ∷ [ 1 ] ]
_ = refl
