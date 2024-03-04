module Algebra.BigOps where

open import Level using (Level)
open import Function
open import Algebra
import Data.Sum as Sum
open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Fin as F using (Fin; _≟_; zero; suc; punchIn)
open import Data.Fin.Properties
open import Data.Vec.Functional
open import Data.Vec.Functional.Properties
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong)
open import Relation.Nullary.Decidable
open import Vector.Properties
open import Relation.Binary
open import Relation.Nullary

open import Algebra.Ring.Properties
open import Vector

private variable
  a ℓ : Level
  m n : ℕ

module SumRawMonoid (rawMonoid : RawMonoid a ℓ) where

  open RawMonoid rawMonoid renaming (Carrier to A)

  private variable
    V W : Vector A n

  ∑ : Vector A n → A
  ∑ = foldr _∙_ ε

module SumRawRing (rawRing : RawRing a ℓ) where

  open RawRing rawRing renaming (Carrier to A)
  open SumRawMonoid +-rawMonoid public

  δ : (i j : Fin n) → A
  δ i j with i ≟ j
  ... | true  because _ = 1#
  ... | false because _ = 0#

  δss≡δ : (i j : Fin n) → δ (suc i) (suc j) ≡ δ i j
  δss≡δ i j with i ≟ j
  ... | true  because _ = ≡.refl
  ... | false because _ = ≡.refl

module SumMonoid (monoid : Monoid a ℓ) where

  open Monoid monoid renaming (Carrier to A)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open SumRawMonoid rawMonoid public

  ∑0r : ∀ n → ∑ {n} (const ε) ≈ ε
  ∑0r zero = refl
  ∑0r (suc n) = begin
    ∑ {suc n} (const ε) ≈⟨ ∙-congˡ (∑0r n) ⟩
    ε ∙ ε               ≈⟨ identityˡ ε ⟩
    ε ∎

  ∑Ext : {U V : Vector A n} → U ≋ V → ∑ U ≈ ∑ V
  ∑Ext {zero} U≈V = refl
  ∑Ext {suc n} {U} {V} U≈V = begin
    head U ∙ ∑ (tail U) ≈⟨ ∙-cong (U≈V F.zero) (∑Ext (U≈V ∘ suc)) ⟩
    head V ∙ ∑ (tail V) ∎

module SumCommMonoid (cMonoid : CommutativeMonoid a ℓ) where

  open CommutativeMonoid cMonoid renaming (Carrier to A)
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open SumMonoid monoid public
  open import Algebra.Solver.CommutativeMonoid cMonoid using (solve; _⊜_; _⊕_)


  ∑Split : (V W : Vector A n) → ∑ (λ i → V i ∙ W i) ≈ ∑ V ∙ ∑ W
  ∑Split {zero} V W = sym (identityʳ _)
  ∑Split {suc n} V W = begin
    head V ∙ head W ∙ ∑ (λ i → tail V i ∙ tail W i) ≈⟨ ∙-congˡ (∑Split (tail V) (tail W)) ⟩
    head V ∙ head W ∙ (∑ (tail V) ∙ ∑ (tail W)) ≈⟨ helper (head V) (head W) (∑ (tail V)) (∑ (tail W)) ⟩
    ∑ V ∙ ∑ W ∎ where

    helper : ∀ a b c d → a ∙ b ∙ (c ∙ d) ≈ ((a ∙ c) ∙ (b ∙ d))
    helper = solve 4 (λ a b c d → ((a ⊕ b) ⊕ (c ⊕ d)) ⊜ ((a ⊕ c) ⊕ (b ⊕ d))) refl

  ∑Split++ : (V : Vector A m) (W : Vector A n) → ∑ (V ++ W) ≈ ∑ V ∙ ∑ W
  ∑Split++ {zero} V W = sym (identityˡ _)
  ∑Split++ {suc m} V W = begin
    ∑ (V ++ W) ≈⟨ ∑Ext {U = V ++ W} {V = (V F.zero ∷ tail V) ++ W}
      (λ i → reflexive (++-cong V (head V ∷ tail V)
      (λ i → ≡.sym (head++tail≡id V i) ) (λ _ → ≡.refl) i)) ⟩
    ∑ ((V F.zero ∷ tail V) ++ W) ≈⟨ ∑Ext (reflexive ∘ ++-split (V F.zero) (tail V) W) ⟩
    V F.zero ∙ ∑ (tail V ++ W) ≈⟨ ∙-congˡ (∑Split++ (tail V) W) ⟩
    (V F.zero ∙ (∑ (tail V) ∙ ∑ W)) ≈˘⟨ assoc _ _ _ ⟩
    (∑ V ∙ ∑ W) ∎

  ∑Remove : ∀ (V : Vector A $ suc n) i → ∑ V ≈ V i ∙ ∑ (removeAt V i)
  ∑Remove V zero = refl
  ∑Remove {ℕ.suc _} V (suc i) = begin
    (V zero ∙ ∑ tV)                       ≈⟨ ∙-congˡ $ ∑Remove tV i ⟩
    (V zero ∙ (tV i ∙ ∑ (removeAt tV i))) ≈⟨ helper _ _ _ ⟩
    (tV i ∙ (V zero ∙ ∑ (removeAt tV i))) ∎
    where
    tV = tail V
    helper : ∀ a b c → a ∙ (b ∙ c) ≈ b ∙ (a ∙ c)
    helper = solve 3 (λ a b c → (a ⊕ (b ⊕ c)) ⊜ (b ⊕ (a ⊕ c))) refl

  ∑Remove₂ : ∀ (V : Vector A n) i → ∑ V ≈ V i ∙ ∑ (V [ i ]≔ ε)
  ∑Remove₂ V zero = ∙-congˡ (sym (identityˡ _))
  ∑Remove₂ {ℕ.suc _} V (suc i) = begin
    (V zero ∙ ∑ tV )                    ≈⟨ (∙-congˡ $ ∑Remove₂ tV i) ⟩
    (V zero ∙ (tV i ∙ ∑ (tV [ i ]≔ ε))) ≈⟨ helper _ _ _ ⟩
    (tV i ∙ (V zero ∙ ∑ (tV [ i ]≔ ε))) ∎
    where
    tV = tail V
    helper : ∀ a b c → a ∙ (b ∙ c) ≈ b ∙ (a ∙ c)
    helper = solve 3 (λ a b c → (a ⊕ (b ⊕ c)) ⊜ (b ⊕ (a ⊕ c))) refl

  private
    helperF : ∀ (i : Fin $ ℕ.suc n) j → i F.≤ j → punchIn i j ≡ suc j
    helperF zero j i<j = ≡.refl
    helperF (suc i) (suc j) i≤j = cong suc (helperF _ j (ℕ.≤-pred i≤j))

    pred : Fin (suc (suc n)) → Fin (suc n)
    pred zero = zero
    pred (suc x) = x

    pij≢sj : ∀ i j (i≤j : i F.≤ j) (k : Fin n) → punchIn i (punchIn j k) ≢ suc j
    pij≢sj zero zero z≤n _ ()
    pij≢sj zero (suc zero) z≤n zero ()
    pij≢sj zero (suc zero) z≤n (suc k) ()
    pij≢sj zero j@(suc (suc _)) z≤n k eq = punchInᵢ≢i j _ (cong pred eq)
    pij≢sj (suc i) (suc j) (s≤s i≤j) (suc k) eq = pij≢sj _ _ i≤j _ (cong pred eq)

  ∑Swap< : ∀ (V : Vector A n) i j (i<j : i F.< j) → ∑ (swapV V i j) ≈ ∑ V
  ∑Swap< {suc zero} V zero zero ()
  ∑Swap< {suc (suc n)} V i (suc j) i<j = begin
    ∑ sv ≈⟨ ∑Remove sv i ⟩
    (sv i ∙ ∑ svr) ≈⟨ ∙-congˡ (∑Remove svr j) ⟩
    (sv i ∙ (svr j ∙ ∑ svrr)) ≈⟨ helper (sv i) (svr j) _ ⟩
    (svr j ∙ (sv i ∙ ∑ svrr)) ≈⟨ ∙-cong
      (begin
        svr j ≡⟨ cong ((V [ i ]≔ V (suc j)) [ suc j ]≔ V i)
          (helperF _ j (ℕ.≤-pred i<j))  ⟩
        ((V [ i ]≔ V (suc j)) [ suc j ]≔ V i) (suc j) ≡⟨ updateAt-updates (suc j) (V [ i ]≔ V (suc j)) ⟩
        V i ∎)
      (∙-cong (begin
                 sv i ≡⟨ updateAt-minimal i (suc j) _ (<⇒≢ i<j) ⟩
                 (V [ i ]≔ V (suc j)) i ≡⟨ updateAt-updates i V ⟩
                 V (suc j) ≡˘⟨ cong V (helperF i j (ℕ.≤-pred i<j)) ⟩
                 vr j ∎)
              (∑Ext (λ k → let pij = punchIn i (punchIn j k) in begin
                svrr k ≡⟨ updateAt-minimal pij (suc j) _ (pij≢sj i j (ℕ.≤-pred i<j) k) ⟩
                (V [ i ]≔ V (suc j)) pij ≡⟨ updateAt-minimal pij i _ (punchInᵢ≢i _ _) ⟩
                vrr k ∎))) ⟩
    (V i ∙ (vr j ∙ ∑ vrr)) ≈˘⟨ ∙-congˡ (∑Remove vr j) ⟩
    (V i ∙ ∑ vr) ≈˘⟨ ∑Remove V i ⟩
    ∑ V ∎
    where
    sv = swapV V i (suc j)
    svr = removeAt sv i
    svrr = removeAt svr j

    vr = removeAt V i
    vrr = removeAt vr j

    helper : ∀ a b c → a ∙ (b ∙ c) ≈ b ∙ (a ∙ c)
    helper = solve 3 (λ a b c → (a ⊕ (b ⊕ c)) ⊜ (b ⊕ (a ⊕ c))) refl

  ∑Swap : ∀ (V : Vector A n) i j → ∑ (swapV V i j) ≈ ∑ V
  ∑Swap {n = n} V i j with <-cmp i j
  ... | tri< i<j _ _ = ∑Swap< V i j i<j
  ... | tri> _ _ i>j = trans (∑Ext λ k → reflexive (swap-exchange V i j k)) (∑Swap< V j i i>j)
  ... | tri≈ _ ≡.refl _ = ∑Ext {n} $ reflexive ∘ helper
    where
    helper : ∀ k → (V [ i ]≔ V i [ i ]≔ V i) k ≡ V k
    helper k with k F.≟ i
    ... | yes ≡.refl = updateAt-updates i _
    ... | no k≢i = ≡.trans (updateAt-minimal k _ _ k≢i) (updateAt-minimal k _ _ k≢i)


module SumRing (ring : Ring a ℓ) where

  open Ring ring renaming (Carrier to A)
  open SumRawRing rawRing
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
  open import Vector.Setoid.Properties setoid hiding (++-cong)
  open Units ring
  open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid using (solve; _⊜_; _⊕_)
  open SumCommMonoid +-commutativeMonoid public
    using (∑0r; ∑Ext; ∑Split; ∑Split++; ∑Swap<; ∑Swap)

  ∑Mulrdist : (x : A) (V : Vector A n)
             → x * ∑ V ≈ ∑ λ i → x * V i
  ∑Mulrdist {zero} x V = 0RightAnnihilates x
  ∑Mulrdist {suc _} x V = begin
    x * ∑ V                       ≈⟨ distribˡ x (V F.zero) _ ⟩
    x * V F.zero + x * ∑ (tail V) ≈⟨ +-congˡ (∑Mulrdist x (tail V)) ⟩
    x * V F.zero + ∑ (λ i → x * V (F.suc i)) ∎

  ∑Mulldist : (x : A) (V : Vector A n)
            → (∑ V) * x ≈ ∑ λ i → V i * x
  ∑Mulldist {zero} x V = 0LeftAnnihilates x
  ∑Mulldist {suc _} x V = begin
    ∑ V * x                       ≈⟨ distribʳ x (V F.zero) _ ⟩
    V F.zero * x + ∑ (tail V) * x ≈⟨ +-congˡ (∑Mulldist x (tail V)) ⟩
    (∑ λ i → V i * x) ∎

  ∑Mul0r : (V : Vector A n) → ∑ (λ i → 0# * V i) ≈ 0#
  ∑Mul0r V = begin
    ∑ (λ i → 0# * V i) ≈˘⟨ ∑Mulrdist 0# V ⟩
    0# * ∑ V            ≈⟨ 0LeftAnnihilates _ ⟩
    0# ∎

  ∑Mul1r : (V : Vector A n) (j : Fin n) → ∑ (λ i → δ j i * V i) ≈ V j
  ∑Mul1r {suc n} V zero = begin
    1# * V F.zero + (∑ λ i → δ F.zero (suc i) * tail V i) ≈⟨ +-congʳ (*-identityˡ _ ) ⟩
    V F.zero + (∑ λ i → δ F.zero (suc i) * tail V i) ≈⟨ +-congˡ (∑Mul0r (tail V)) ⟩
    V F.zero + 0# ≈⟨ +-identityʳ _ ⟩
    V F.zero ∎
  ∑Mul1r {suc n} V (suc j) = begin
    0# * _ + _                             ≈⟨ +-congʳ (0LeftAnnihilates _) ⟩
    0# + _                                 ≈⟨ +-identityˡ _ ⟩
    ∑ (λ i → δ (suc j) (suc i) * tail V i) ≈⟨ ∑Ext (λ i → *-congʳ (reflexive $ δss≡δ j i)) ⟩
    ∑ (λ i → δ j i * tail V i)             ≈⟨ ∑Mul1r (tail V) j ⟩
    tail V j ∎



