# Library Explanation

The main feature of this library is to normalize matrices.

```agda
open import Data.Product
open import Data.Maybe
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Algebra.MatrixData
```

We start by importing a Matrix, that is vector of vectors.

So for example, a matrix of natural numbers.

```agda
matrix : Matrix ℕ 2 2
matrix = (1 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷ []
```

After the normalization, the new matrix should be:

```agda
normedMatrix : Matrix ℕ 2 2
normedMatrix = (1 ∷ 0 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ []
```

## System of equations

```agda
A : Matrix ℕ 2 2
A = (1 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷ []

b : Vec ℕ 2
b = 2 ∷ 3 ∷ []
```

We want to solve the system A*x = b.

that means:

x = 2
x + y = 3

We do that by appending A with b and after, doing the normalization.

```agda
A++b : Matrix ℕ 2 3
A++b = (1 ∷ 0 ∷ 2 ∷ []) ∷ (1 ∷ 1 ∷ 3 ∷ []) ∷ []
```

After the normalization, the result is:

```agda
A++b-normed : Matrix ℕ 2 3
A++b-normed = (1 ∷ 0 ∷ 2 ∷ []) ∷ (0 ∷ 1 ∷ 1 ∷ []) ∷ []
```

the first row means:
1*x + 0*y = 2
0*x + 1*y = 1

that is the same of:
x = 2
y = 1

And we solve the system.


** Using the library in Agda programs

This library have some features to use in other Agda programs.
For example:

```agda
propsXY : (x y : ℕ) → Set _
propsXY x y = x ≡ 2 × x + y ≡ 3
```

After solving the system of equations, we want that the solutions have the properties of the system of the equations.

```agda
findSolutionWithPropType = Maybe (Σ[ v₁ ∈ ℕ ] Σ[ v₂ ∈ ℕ ] (∀ x y → x ≡ v₁ × y ≡ v₂ × propsXY x y))
```

The program maybe find a solution that respect the project.

*** Stronger property

The last function is not so much useful because the function can maybe return a result.
It means that it can return nothing all the time and it is still type checkes.

In this library, it is possible to write this property instead:

```agda
findSolutionType = ∀ x y → x ≡ 2 → x + y ≡ 3 → Σ[ v₁ ∈ ℕ ] Σ[ v₂ ∈ ℕ ] (x ≡ v₁ × y ≡ v₂)
```

To make this function, it is necessary to prove that normalization of the system of the equations is correct.
