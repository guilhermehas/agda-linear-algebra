{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.DecidableField

module SystemEquations.VecPiv {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit
open import Data.Product
open import Data.Maybe using (Is-just; Maybe; just; nothing)
open import Data.Sum renaming ([_,_] to [_∙_])
open import Data.Empty
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Nat.Properties as ℕ using (module ≤-Reasoning)
open import Data.Fin as F using (Fin; suc; splitAt; fromℕ; toℕ; inject₁)
open import Data.Fin.Properties as F
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Nullary

open import Fin.Base
open import Fin.Properties
open import Vector.Structures
open import Vector.Properties
open import Algebra.Matrix.Structures
open import SystemEquations.Definitions dField
open import MatrixFuncNormalization.Definitions dField
import Algebra.Module.Definition as MDefinition
import Algebra.Module.Props as MProps′
open import Algebra.BigOps

open DecidableField dField renaming (Carrier to F) hiding (sym)
open HeytingField heytingField using (heytingCommutativeRing)
open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (rawRing; ring; sym; +-commutativeMonoid)
open import Algebra.Properties.Ring ring
open VRing rawRing
open import Algebra.Module.Instances.AllVecLeftModule ring using (leftModule)
open MRing rawRing using (Matrix)
open import Algebra.Module.Instances.CommutativeRing commutativeRing
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; subst; subst₂; cong)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Solver.CommutativeMonoid +-commutativeMonoid hiding (id)
open import Algebra.Module.PropsVec commutativeRing hiding (module MProps)

open import lbry

private
  open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)
open SumRing ring using (∑Ext; ∑0r; δ; ∑Mul1r; ∑Split)
open MDef′

private variable
  m n : ℕ

allRowsNormed[] : ∀ n → AllRowsNormalized≁0 {n} []
allRowsNormed[] n {()}

vecIn→vecBool : Vector (Fin n) m → Vector Bool n
vecIn→vecBool {m = ℕ.zero} xs i = false
vecIn→vecBool {m = ℕ.suc m} xs 0F with xs 0F
... | 0F = true
... | suc c = false
vecIn→vecBool {m = ℕ.suc m} xs (suc {ℕ.suc n} i) with xs 0F
... | 0F = vecIn→vecBool (λ j → predFin (xs (suc j))) i
... | suc c = vecIn→vecBool (λ j → predFin (xs j)) i

private
  testV : Vector (Fin 5) 2
  testV 0F = 1F
  testV 1F = 3F

  vResult = vecIn→vecBool testV

+-right : ∀ m p → m ℕ.+ ℕ.suc p ≡ ℕ.suc (m ℕ.+ p)
+-right ℕ.zero p = ≡.refl
+-right (ℕ.suc m) p rewrite +-right m p = ≡.refl

qtTrue : Vector Bool n → ℕ
qtTrue {ℕ.zero} xs = ℕ.zero
qtTrue {ℕ.suc n} xs = let v = (qtTrue (tail xs)) in if xs 0F then ℕ.suc v else v

vecIn→vecBool-qtTrue : (xs : Vector (Fin n) m) (normed : AllRowsNormalized≁0 xs) → qtTrue (vecIn→vecBool xs) ≡ m
vecIn→vecBool-qtTrue {ℕ.zero} {ℕ.zero} _ _ = ≡.refl
vecIn→vecBool-qtTrue {ℕ.suc n} {ℕ.zero} _ _ = vecIn→vecBool-qtTrue {n} [] (allRowsNormed[] n)
vecIn→vecBool-qtTrue {ℕ.zero} {ℕ.suc m} xs _ with () ← xs 0F
vecIn→vecBool-qtTrue {ℕ.suc ℕ.zero} {ℕ.suc ℕ.zero} xs _ with xs 0F
... | 0F = ≡.refl
vecIn→vecBool-qtTrue {ℕ.suc ℕ.zero} {ℕ.suc (ℕ.suc m)} xs normed with xs 0F | xs 1F | normed {y = 1F} (ℕ.s≤s ℕ.z≤n)
... | 0F | 0F | ()
vecIn→vecBool-qtTrue {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs normed with vecIn→vecBool-qtTrue (predFin ∘ xs) | xs 0F in eqx
... | _ | 0F rewrite vecIn→vecBool-qtTrue (predFin ∘ xs ∘ suc) {!!} = ≡.refl
... | vBefore | suc c rewrite vBefore {!!} = ≡.refl

module _ {xs : Vector (Fin $ ℕ.suc n) $ ℕ.suc m} where

  module EqXs (eqXs : xs 0F ≡ 0F) where
    tailXs>0 : ∀ (normed : AllRowsNormalized≁0 xs) i → toℕ (tail xs i) ℕ.> 0
    tailXs>0 normed i = <.begin-strict
      0                <.≡˘⟨ cong toℕ eqXs ⟩
      toℕ (xs 0F)       <.<⟨ normed (ℕ.s≤s ℕ.z≤n) ⟩
      toℕ (xs (F.suc i)) <.∎
      where module < = ≤-Reasoning

    ysPiv : .(normed : AllRowsNormalized≁0 xs) → Vector (Fin n) m
    ysPiv normed i = F.reduce≥ (tail xs i) (tailXs>0 normed i)

    allRowsNormed : (normed : AllRowsNormalized≁0 xs) → AllRowsNormalized≁0 (ysPiv normed)
    allRowsNormed normed {x} {y} x<y
      rewrite toℕ-reduce≥ _ (tailXs>0 normed x) | toℕ-reduce≥ _ (tailXs>0 normed y) = <.begin
        ℕ.suc (ℕ.pred (toℕ (tail xs x))) <.≡⟨ suc-pred (tailXs>0 normed _) ⟩
        toℕ (xs (suc x)) <.≤⟨ ℕ.∸-monoˡ-≤ 1 (normed (ℕ.s≤s x<y)) ⟩
        toℕ (xs (suc y)) ∸ 1 <.∎
      where module < = ≤-Reasoning

  module NEqXs (xs0F≢0F : xs 0F ≢ 0F) where
    tailXs>0 : ∀ (normed : AllRowsNormalized≁0 xs) i → toℕ (tail xs i) ℕ.> 0
    tailXs>0 normed i = <.begin-strict
      0                 <.<⟨ ≤∧≢⇒< ℕ.z≤n (xs0F≢0F ∘ ≡.sym) ⟩
      toℕ (xs 0F)       <.<⟨ normed (ℕ.s≤s ℕ.z≤n) ⟩
      toℕ (xs (F.suc i)) <.∎
      where module < = ≤-Reasoning

    ysPiv : .(normed : AllRowsNormalized≁0 xs) → Vector (Fin n) m
    ysPiv normed i = F.reduce≥ (tail xs i) (tailXs>0 normed i)

    allRowsNormed : (normed : AllRowsNormalized≁0 xs) → AllRowsNormalized≁0 (ysPiv normed)
    allRowsNormed normed {x} {y} x<y
      rewrite toℕ-reduce≥ _ (tailXs>0 normed x) | toℕ-reduce≥ _ (tailXs>0 normed y) = <.begin
        ℕ.suc (ℕ.pred (toℕ (tail xs x))) <.≡⟨ suc-pred (tailXs>0 normed _) ⟩
        toℕ (xs (suc x)) <.≤⟨ ℕ.∸-monoˡ-≤ 1 (normed (ℕ.s≤s x<y)) ⟩
        toℕ (xs (suc y)) ∸ 1 <.∎
      where module < = ≤-Reasoning

normed≥ : {xs : Vector (Fin n) m} (normed : AllRowsNormalized≁0 xs) → n ℕ.≥ m
normed≥ {ℕ.zero} {ℕ.zero} {xs} normed = ℕ.z≤n
normed≥ {ℕ.zero} {ℕ.suc m} {xs} normed with () ← xs 0F
normed≥ {ℕ.suc n} {ℕ.zero} {xs} normed = ℕ.z≤n
normed≥ {ℕ.suc n} {ℕ.suc m} {xs} normed with xs 0F F.≟ 0F
... | yes xs0≡0 = ℕ.s≤s (normed≥ {xs = ysPiv xs0≡0 normed} (allRowsNormed xs0≡0 normed))
  where open EqXs
... | no  xs0≢0 = ℕ.s≤s (normed≥ {xs = ysPiv xs0≢0 normed} (allRowsNormed xs0≢0 normed))
  where open NEqXs

normed> : {xs : Vector (Fin $ ℕ.suc n) (ℕ.suc m)} (normed : AllRowsNormalized≁0 xs)
  (xs≢0F : xs 0F ≢ 0F) → n ℕ.> m
normed> {ℕ.zero} {xs = xs} normed xs≢0F with xs 0F in eqn
... | 0F with () ← xs≢0F ≡.refl
normed> {ℕ.suc n} {ℕ.zero} normed xs≢0F = ℕ.s≤s ℕ.z≤n
normed> {ℕ.suc n} {ℕ.suc m} {xs} normed xs≢0F with xs 1F in eq1F | normed {0F} {1F} (ℕ.s≤s ℕ.z≤n)
... | 0F | ()
... | 1F | ℕ.s≤s m≤n = contradiction (toℕ-injective (ℕ.≤-antisym m≤n ℕ.z≤n)) xs≢0F
... | suc (suc c) | _ = ℕ.s≤s norm
  where
  open NEqXs

  tNormed = tailXs>0 {xs = xs} xs≢0F normed 0F

  ysPiv≢0 : F.reduce≥ {m = 1} (xs 1F) tNormed ≢ 0F
  ysPiv≢0 ysPiv≡0 = ℕ.0≢1+n $ N.begin-equality
    0                               N.≡˘⟨ cong toℕ ysPiv≡0 ⟩
    toℕ (F.reduce≥ (xs 1F) tNormed) N.≡⟨ toℕ-reduce≥ (xs 1F) tNormed ⟩
    toℕ (xs 1F) ∸ 1                 N.≡⟨ cong (λ x → toℕ x ∸ 1) eq1F ⟩
    ℕ.suc (toℕ c)                   N.∎
    where module N = ≤-Reasoning

  norm = normed> {xs = ysPiv xs≢0F normed} (allRowsNormed xs≢0F normed) ysPiv≢0

private
  n∸m-suc : n ℕ.≥ m → ℕ.suc n ∸ m ≡ ℕ.suc (n ∸ m)
  n∸m-suc ℕ.z≤n = ≡.refl
  n∸m-suc (ℕ.s≤s n≥m) = n∸m-suc n≥m

rPivs : (xs : Vector (Fin n) m) → ∃ (Vector (Fin n))
rPivs {ℕ.zero} {ℕ.zero} xs = ℕ.zero , []
rPivs {ℕ.zero} {ℕ.suc m} xs with () ← xs 0F
proj₁ (rPivs {ℕ.suc n} {ℕ.zero} xs) = _
proj₂ (rPivs {ℕ.suc n} {ℕ.zero} xs) i = i
rPivs {ℕ.suc ℕ.zero} {ℕ.suc m} xs = ℕ.zero , const 0F
rPivs {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs with xs 0F | rPivs (predFin ∘ xs)
... | 0F | _ = _ , suc ∘ (proj₂ (rPivs $ predFin ∘ (tail xs)))
... | suc _ | _ , ys = _ , 0F ∷ suc ∘ ys

rPivs-n∸m : (xs : Vector (Fin n) m) (normed : AllRowsNormalized≁0 xs) → rPivs xs .proj₁ ≡ n ∸ m
rPivs-n∸m {ℕ.zero} {ℕ.zero} xs _ = ≡.refl
rPivs-n∸m {ℕ.zero} {ℕ.suc m} xs normed with () ← xs 0F
rPivs-n∸m {ℕ.suc n} {ℕ.zero} xs normed = ≡.refl
rPivs-n∸m {ℕ.suc ℕ.zero} {ℕ.suc m} xs normed = ≡.sym (ℕ.m≤n⇒m∸n≡0 {n = m} ℕ.z≤n)
rPivs-n∸m {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs normed with xs 0F in eqXs0 | rPivs-n∸m (predFin ∘ xs)
... | 0F | _ rewrite rPivs-n∸m (predFin ∘ tail xs) {!!} = ≡.refl
... | suc c | f-normed rewrite f-normed {!!} = ≡.sym (n∸m-suc {n = n} {m = m}
  (ℕ.≤-pred (normed> {xs = xs} normed λ eqXs → contradiction (≡.trans (≡.sym eqXs) eqXs0) 0≢1+n)))

∑-pivs-same : (xs : Vector (Fin n) m) (g : Fin n → F) (normed : AllRowsNormalized≁0 xs)
   → ∑ (g ∘ xs) + ∑ (g ∘ rPivs xs .proj₂) ≈ ∑ g
∑-pivs-same {ℕ.zero} {ℕ.zero} xs g normed = +-identityˡ _
∑-pivs-same {ℕ.zero} {ℕ.suc m} xs g normed with () ← xs 0F
∑-pivs-same {ℕ.suc n} {ℕ.zero} xs g normed = +-identityˡ _
∑-pivs-same {ℕ.suc ℕ.zero} {ℕ.suc m} xs g normed = {!!}
∑-pivs-same {ℕ.suc n@(ℕ.suc n′)} {ℕ.suc m} xs g normed with ∑-pivs-same {n} {ℕ.suc m} (predFin ∘ xs) (tail g) | xs 0F in eqXs
... | _ | 0F = begin
  _ + _ + _ ≈⟨ +-assoc _ _ _ ⟩
  g 0F + (∑ (g ∘ tail xs) + _) ≈⟨ {!!} ⟩
  g 0F + (∑ (g ∘ suc ∘ predFin ∘ tail xs) + ∑ (g ∘ suc ∘ rPivs (predFin ∘ tail xs) .proj₂))
    ≈⟨ +-congˡ (∑-pivs-same {n} {m} (predFin ∘ xs ∘ suc) (g ∘ suc) {!!} ) ⟩
  g 0F + ∑ (tail g) ∎

... | peq | suc c = begin
  _ + (g 0F + _) ≈⟨ solve 3 (λ a b c → a ⊕ b ⊕ c , b ⊕ a ⊕ c) refl _ (g 0F) _ ⟩
  g 0F + (g (suc c) + ∑ (g ∘ xs ∘ suc) + ∑ (g ∘ suc ∘ rPivs (predFin ∘ xs) .proj₂) ) ≈⟨ +-congˡ (+-congʳ
    (+-cong (reflexive (cong g sc≡xs0)) {!!})) ⟩
  -- {!!} ≈⟨ {!!} ⟩
  g 0F + (g (suc (predFin (xs 0F))) + ∑ (g ∘ suc ∘ predFin ∘ xs ∘ suc) + ∑ (g ∘ suc ∘ rPivs (predFin ∘ xs) .proj₂))
    ≈⟨ +-congˡ (peq {!!}) ⟩
  g 0F + ∑ (tail g) ∎
  where
  sc≡xs0 : suc c ≡ suc (predFin (xs 0F))
  sc≡xs0 rewrite eqXs = ≡.refl

vSplit : (xs : Vector (Fin n) m) → Vector (ℕ ⊎ Fin m) n
vSplit {ℕ.suc n} {ℕ.zero} xs i = inj₁ ℕ.zero
vSplit {ℕ.suc n} {ℕ.suc m} xs 0F with xs 0F
... | 0F = inj₂ 0F
... | suc c = inj₁ ℕ.zero
vSplit {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs (suc i) with xs 0F
... | 0F = [ inj₁ ∘ ℕ.suc ∙ inj₂ ∘ suc ] (vSplit (predFin ∘ tail xs) i)
... | suc c = [ inj₁ ∘ ℕ.suc ∙ inj₂ ] (vSplit (predFin ∘ xs) i)

private
  vSplitTest = vSplit testV

vSplitFirst<n∸m : ∀ (xs : Vector (Fin n) m) i (normed : AllRowsNormalized≁0 xs) (is₁ : IsInj₁ (vSplit xs i))
  → fromIsInj₁ is₁ ℕ.< n ∸ m
vSplitFirst<n∸m {ℕ.suc n} {ℕ.zero} xs i normed is₁ = ℕ.s≤s ℕ.z≤n
vSplitFirst<n∸m {ℕ.suc n} {ℕ.suc m} xs 0F normed is₁ with xs 0F
... | suc c = {!!}
vSplitFirst<n∸m {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs (suc i) normed with xs 0F in eqXs
  | vSplit (predFin ∘ xs) i in eqPred
  | vSplitFirst<n∸m (predFin ∘ xs) i

... | 0F | _ | f = {!!}
... | suc a | inj₁ p | f rewrite eqPred = λ _ → ℕ.≤-trans (ℕ.s≤s (f {!!} _))
  (ℕ.≤-reflexive (≡.sym (n∸m-suc {n} {m}
    (ℕ.≤-pred $ normed> normed λ xs0≡0 → 0≢1+n (≡.trans (≡.sym xs0≡0) eqXs)))))
... | suc a | inj₂ p | f rewrite eqPred = λ ()

vSplit-same : ∀ (xs : Vector (Fin n) m) i (normed : AllRowsNormalized≁0 xs) →
  vSplit {n} {m} xs (xs i) ≡ inj₂ i
vSplit-same {ℕ.zero} {ℕ.suc m} xs i normed with () ← xs 0F
vSplit-same {ℕ.suc ℕ.zero} {ℕ.suc m} xs 0F normed with xs 0F in eq0
... | 0F rewrite eq0 = ≡.refl
vSplit-same {ℕ.suc ℕ.zero} {ℕ.suc m} xs (suc i) normed = {!!}
vSplit-same {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs 0F normed with xs 0F in eq0 | vSplit-same (predFin ∘ xs) 0F
... | 0F | b rewrite eq0 = ≡.refl
... | suc c | f rewrite eq0 | f {!!} = ≡.refl
vSplit-same {ℕ.suc (ℕ.suc n)} {ℕ.suc m} xs (suc i) normed with
  xs 0F in eq0 |
  vSplit-same (predFin ∘ xs) |
  vSplit-same (predFin ∘ tail xs) |
  xs (suc i) in eqS
... | 0F | f | g | 0F = {!!}
... | 0F | f | g | suc p rewrite eq0 = help2

  where
  help : vSplit (λ x → predFin (xs (suc x))) (predFin (xs (suc i))) ≡ inj₂ i
    → vSplit (λ x → predFin (xs (suc x))) p ≡ inj₂ i
  help rewrite eqS = id

  help2 : [ inj₁ ∘ ℕ.suc ∙ inj₂ ∘ suc ] (vSplit (predFin ∘ tail xs) p) ≡ inj₂ (suc i)
  help2 rewrite help (g i {!!}) = ≡.refl

... | suc c | f | g | 0F rewrite eq0 = {!!}
... | suc c | f | g | suc p rewrite eq0 = help2
  where
  help : vSplit (predFin ∘ xs) (predFin (xs (suc i))) ≡ inj₂ (suc i)
    → vSplit (predFin ∘ xs) p ≡ inj₂ (suc i)
  help rewrite eqS = id

  help2 : [ inj₁ ∘ ℕ.suc ∙ inj₂ ] (vSplit (predFin ∘ xs) p) ≡ inj₂ (suc i)
  help2 rewrite help (f (suc i) {!!}) = ≡.refl
