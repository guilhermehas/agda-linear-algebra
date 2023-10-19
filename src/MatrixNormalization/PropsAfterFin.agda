module MatrixNormalization.PropsAfterFin where

open import Function using (_∘_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Fin as F
open import Data.Fin.Properties as F
open import Data.Fin.Induction
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import lbry
open import MatrixNormalization.PropsAfter

open module PNormAfter {n} = PropNormAfter (F.<-strictTotalOrder n)

open ≡-Reasoning

private variable
  n : ℕ
  i j : Fin n
  i<j : i < j
  xs : Vec (Fin n) n

AlwaysEqual : (xs : Vec (Fin n) n) → Set
AlwaysEqual xs = ∀ i → lookup xs i ≡ i

GreaterThanI : (xs : Vec (Fin n) n) → Set
GreaterThanI xs = ∀ i → lookup xs i ≥ i

Xs>I≡I : GreaterThanI xs → NormedBeforeI i xs → ∀ {k} → k > i → lookup xs k ≡ k
Xs>I≡I {ℕ.suc _} {xs} xi≥i nbef {k} k>i = >-weakInduction P Pn PPred _ ≤-refl
  where

  P : Fin _ → _
  P p = p ≥ k → lookup xs p ≡ p

  Pn : P (fromℕ _)
  Pn _ = ≤-antisym (≤fromℕ _) (xi≥i _)

  PPred : ∀ p → P (suc p) → P (inject₁ p)
  PPred p Ps p≥k = ≤-antisym (ℕ.≤-pred xsp≤sp) lp≥p where

    ip = inject₁ p

    lp≥p : lookup xs ip ≥ ip
    lp≥p = xi≥i _

    lp<i : lookup xs ip < lookup xs (suc p)
    lp<i = nbef (suc p) (<-trans k>i (s≤s (cong≤ˡ p≥k (toℕ-inject₁ _)))) ip
      (s≤s (ℕ.≤-reflexive (toℕ-inject₁ _)))

    lsp≡ip : toℕ (lookup xs (suc p)) ≡ ℕ.suc (toℕ ip)
    lsp≡ip rewrite toℕ-inject₁ p | Ps (ℕ.m≤n⇒m≤1+n p≥k) = refl

    xsp≤sp : ℕ.suc (toℕ (lookup xs ip)) ℕ.≤ ℕ.suc (toℕ ip)
    xsp≤sp = ℕ.≤-trans lp<i (ℕ.≤-reflexive lsp≡ip)

XsI≡I : GreaterThanI xs → NormedBeforeI i xs → lookup xs i ≡ i
XsI≡I {ℕ.suc _} {xs} {i} xi≥i nbef with i ≟ fromℕ _
... | yes refl = ≤-antisym (≤fromℕ _) (xi≥i _)
... | no i≠n-1 = ≤-antisym (ℕ.≤-pred li) (xi≥i _)
  where

  siΣ = <→Σinject (≤∧≢⇒< (≤fromℕ _) i≠n-1)
  si = siΣ .proj₁

  si≡i : inject₁ si ≡ i
  si≡i = siΣ .proj₂

  sucI≤sucSi : toℕ (suc i) ℕ.≤ toℕ (suc si)
  sucI≤sucSi = s≤s (ℕ.≤-reflexive (trans (sym (cong toℕ si≡i)) (toℕ-inject₁ _)))

  li' : lookup xs i F.< lookup xs (suc si)
  li' = nbef (suc si) sucI≤sucSi i sucI≤sucSi

  xsSi≡si : toℕ (lookup xs (suc si)) ≡ toℕ (suc i)
  xsSi≡si = begin
    toℕ (lookup xs (suc si)) ≡⟨ cong toℕ (Xs>I≡I {xs = xs} xi≥i nbef sucI≤sucSi) ⟩
    toℕ (suc si)            ≡˘⟨ cong ℕ.suc (toℕ-inject₁ _) ⟩
    toℕ (suc (inject₁ si))   ≡⟨ cong (toℕ ∘ suc) si≡i ⟩
    toℕ (suc i) ∎

  li : lookup xs i F.< suc i
  li rewrite sym xsSi≡si = li'

xsJ≤xsI : j < i → GreaterThanI xs → NormedBeforeI i xs → lookup xs j ≤ lookup xs i
xsJ≤xsI {ℕ.suc _} {j} {i} {xs} j<i xs≥i nbef with i ≟ fromℕ _
... | yes refl rewrite XsI≡I {xs = xs} xs≥i nbef = ≤fromℕ _
... | no i≠n-1 = subst (lookup xs j ≤_) (sym (XsI≡I {xs = xs} xs≥i nbef)) xsJ≤i
  where
  siΣ = <→Σinject (≤∧≢⇒< (≤fromℕ _) i≠n-1)
  si = siΣ .proj₁

  si≡i : inject₁ si ≡ i
  si≡i = siΣ .proj₂

  i≡si = begin
    toℕ i           ≡˘⟨ cong toℕ si≡i ⟩
    toℕ (inject₁ si) ≡⟨ toℕ-inject₁ si ⟩
    toℕ si ∎

  sucI≤sucSi : toℕ (suc i) ℕ.≤ toℕ (suc si)
  sucI≤sucSi = s≤s (ℕ.≤-reflexive i≡si)

  j<si : j < suc si
  j<si = ℕ.≤-trans j<i (ℕ.m≤n⇒m≤1+n (ℕ.≤-reflexive i≡si))

  xsJ<xssI : lookup xs j < lookup xs (suc si)
  xsJ<xssI = nbef _ sucI≤sucSi _ j<si

  xsJ<si : lookup xs j < suc si
  xsJ<si = subst (lookup xs j <_) (Xs>I≡I {xs = xs} xs≥i nbef sucI≤sucSi) xsJ<xssI

  xsJ≤i : lookup xs j ≤ i
  xsJ≤i = subst (toℕ (lookup xs j) ℕ.≤_) (sym i≡si) (ℕ.≤-pred xsJ<si)

normed→xsI≡i : GreaterThanI xs → AllLinesNormalizedRight xs → AlwaysEqual xs
normed→xsI≡i {ℕ.suc n} {xs} normLeft normed = >-weakInduction {n = n} P Pn PPred
  where
  P : Fin _ → Set _
  P k = lookup xs k ≡ k

  Pn : P (fromℕ _)
  Pn = ≤-antisym (≤fromℕ _) (normLeft _)


  PPred : (i : Fin n) → P (suc i) → P (inject₁ i)
  PPred i Ps = ≤-antisym (ℕ.≤-pred (cong≤ʳ sameI normedI)) (normLeft _)
    where
    normedI : lookup xs (suc i) > lookup xs (inject₁ i)
    normedI = normed (suc i) (inject₁ i) (s≤s (ℕ.≤-reflexive (toℕ-inject₁ i)))

    sameI = begin
      toℕ (lookup xs (suc i)) ≡⟨ cong toℕ Ps ⟩
      toℕ (suc i) ≡˘⟨ cong ℕ.suc (toℕ-inject₁ i) ⟩
      ℕ.suc (toℕ (inject₁ i)) ∎
