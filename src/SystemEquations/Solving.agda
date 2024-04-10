open import Algebra.DecidableField

module SystemEquations.Solving {c ℓ₁ ℓ₂} (dField : DecidableField c ℓ₁ ℓ₂) where

open import Algebra
open import Algebra.Apartness
open import Algebra.Module
open import Function
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Maybe using (Is-just; Maybe; just; nothing)
open import Data.Sum
open import Data.Empty
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Nat.Properties as ℕ using (module ≤-Reasoning)
open import Data.Fin as F using (Fin; suc; splitAt; fromℕ; toℕ; inject₁)
open import Data.Fin.Properties as F
open import Data.Fin.Patterns
open import Data.Vec.Functional
open import Relation.Nullary

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

open module MProps {n} = MProps′ (*ⱽ-commutativeRing n) (leftModule n)
open SumRing ring using (∑Ext; ∑0r; δ; ∑Mul1r; ∑Split)
open MDef′

private variable
  m n : ℕ

private
  lastFin : (n : ℕ) → Fin (n ℕ.+ 1)
  lastFin ℕ.zero = 0F
  lastFin (ℕ.suc n) = suc (lastFin n)

  injF : Fin n → Fin (n ℕ.+ 1)
  injF 0F = 0F
  injF (suc i) = suc (injF i)

  add-1 : Vector F n → Vector F (ℕ.suc n)
  add-1 xs = appendLast xs (- 1#)

A++b⇒systemEquations : Matrix F n (m ℕ.+ 1) → SystemEquations n m
A++b⇒systemEquations xs = record { A = λ i j → xs i (injF j) ; b = λ i → xs i (lastFin _) }

module _ where
  open SystemEquations

  sameSolutionsSE : {sx sy : SystemEquations n m}  → A++b sy ⊆ⱽ A++b sx
    → ∀ v → IsSolutionA++b sx v → IsSolutionA++b sy v
  sameSolutionsSE sy⊆ⱽsx i = sameSolutions {α = i} sy⊆ⱽsx

tail-lemma : ∀ (u : Vector F (ℕ.suc n)) b k → tail (appendLast u b) k ≈ (appendLast (tail u) b) k
tail-lemma u b k = refl

add-1∑ : ∀ (v : Vector F n) b (u : Vector F n) → (add-1 v ∙ⱽ appendLast u b) ≈ u ∙ⱽ v - b
add-1∑ {ℕ.zero} v b u = begin
  - 1# * b + 0# ≈⟨ +-identityʳ _ ⟩
  - 1# * b      ≈⟨ -1*x≈-x _ ⟩
  - b          ≈˘⟨ +-identityˡ (- b) ⟩
  0# + - b ∎
add-1∑ {ℕ.suc n} v b u = begin
  v 0F * u 0F + add-1 (tail v) ∙ⱽ tail (appendLast u b) ≈⟨ +-congʳ (*-comm _ _)⟩
  u 0F * v 0F + add-1 (tail v) ∙ⱽ appendLast (tail u) b ≈⟨ +-congˡ (add-1∑ _ b (tail u)) ⟩
  u 0F * v 0F + (tail u ∙ⱽ tail v - b)             ≈˘⟨ +-assoc _ _ (- b) ⟩
  u 0F * v 0F + tail u ∙ⱽ tail v - b ∎

sameSolutionsA++b : ∀ {sx : SystemEquations n m} {v} (open SystemEquations sx)
  → IsSolutionA++b $ add-1 v → IsSolution v
sameSolutionsA++b {n = n} {m = m} {sx = system A b} {v} sv i = begin
  A i ∙ⱽ v ≈⟨ +-inverseˡ-unique (A i ∙ⱽ v) (- b i) sv-lemma ⟩
  - - b i  ≈⟨ -‿involutive _ ⟩
  b i ∎
  where

  sv-lemma = begin
    A i ∙ⱽ v - b i             ≈˘⟨ add-1∑ v (b i) (A i) ⟩
    add-1 v ∙ⱽ appendLast (A i) (b i) ≈⟨ sv i ⟩
    0# ∎

sameSolutionsA++b-inv : ∀ {sx : SystemEquations n m} {v} (open SystemEquations sx)
  → IsSolution v → IsSolutionA++b $ add-1 v
sameSolutionsA++b-inv {m = m} {system A b} {v} sv i = begin
  add-1 v ∙ⱽ appendLast (A i) (b i) ≈⟨ add-1∑ v _ _ ⟩
  A i ∙ⱽ v - b i                    ≈⟨ +-congʳ (sv i) ⟩
  b i - b i                         ≈⟨ -‿inverseʳ (b i) ⟩
  0# ∎

systemUnsolvable : ∀ {sx : SystemEquations n m} (open SystemEquations sx) → A≈0∧b#0 → ∀ {v} → IsSolution v → ⊥
systemUnsolvable {n = n} {m} {system A b} (i , A0 , b#0) {v} sv = tight _ _ .proj₂
  (begin
    b i             ≈˘⟨ sv i ⟩
    A i ∙ⱽ v         ≈⟨ ∑Ext (λ j → trans (*-congʳ (A0 j)) (zeroˡ _)) ⟩
    ∑ {m} 0ⱽ ≈⟨ ∑0r m ⟩
    0# ∎) b#0

module _ where
  open MatrixIsNormed≁0≈1
  open MatrixIsNormed≁0

  emptyNormed : (A : Matrix F 0 n) → MatrixIsNormed≁0≈1 A
  pivs (isNormed (emptyNormed A)) ()
  mPivots (isNormed (emptyNormed A)) ()
  pivsCrescent (isNormed (emptyNormed A)) {y = ()} x
  columnsZero (isNormed (emptyNormed A)) () j x
  pivsOne (emptyNormed A) ()

systemNormedSplit : ∀ (sx : SystemEquations n m) (open SystemEquations sx) → MatrixIsNormed≁0≈1 A++b
  → A≈0∧b#0 ⊎ MatrixIsNormed≁0≈1 A
systemNormedSplit {ℕ.zero} sx normed = inj₂ (emptyNormed _)
systemNormedSplit {ℕ.suc n} {m} sx (cIsNorm≁0≈1 (cIsNorm≁0 pivs mPivots pivsCrescent columnsZero) pivsOne)
  with pivs (fromℕ n) F.≟ fromℕ m
... | yes p = inj₁ (fromℕ _ , (λ i → A≈0 (mPivots (fromℕ n) .proj₂ (inject₁ i) (inj₁< i)))  , (b#0 $ mPivots (fromℕ _) .proj₁))
  where
  open SystemEquations sx

  b#0 : appendLast (A $ fromℕ n) (b $ fromℕ n) (pivs $ fromℕ n) # 0# → b (fromℕ n) # 0#
  b#0 rewrite p | appendLastFromℕ (A $ fromℕ n) (b $ fromℕ n) = id

  A≈0 : {i : Fin _} → appendLast (A (fromℕ n)) (b (fromℕ n)) (inject₁ i) ≈ 0# → A (fromℕ n) i ≈ 0#
  A≈0 {i} rewrite appendLastInj (A (fromℕ n)) (b (fromℕ n)) i = id

  inj₁< : ∀ i → inject₁ i F.< pivs (fromℕ n)
  inj₁< i = ≡.subst (inject₁ i F.<_) (≡.sym p) (≤∧≢⇒< (≤fromℕ _) (fromℕ≢inject₁ ∘ ≡.sym))
... | no pn≢fromℕ = inj₂ (cIsNorm≁0≈1 (cIsNorm≁0 pivsR mPivotsR allRowsR cols0R) pivs≁0)
  where
  open SystemEquations sx

  pn<n : pivs (fromℕ n) F.< fromℕ _
  pn<n = ≤∧≢⇒< (≤fromℕ _) pn≢fromℕ

  pi≢n : ∀ i → pivs i ≢ fromℕ _
  pi≢n i peq with i F.≟ fromℕ _
  ... | yes ≡.refl = pn≢fromℕ peq
  ... | no i≢fn = <⇒≢ (<-trans (pivsCrescent (≤∧≢⇒< (≤fromℕ _) i≢fn)) pn<n) peq

  toℕ-pi≢n : ∀ i → m ≢ F.toℕ (pivs i)
  toℕ-pi≢n i peq = pi≢n i (toℕ-injective (≡.sym (≡.trans (toℕ-fromℕ _) peq)))

  pivsR : Vector (Fin m) (ℕ.suc n)
  pivsR i = F.lower₁ (pivs i) (toℕ-pi≢n i)

  toℕ-pivR-≡ : ∀ i → toℕ (pivsR i) ≡ toℕ (pivs i)
  toℕ-pivR-≡ i = toℕ-lower₁ _ (toℕ-pi≢n _)

  A++b≡piv : ∀ i → A++b i (pivs i) ≡ A i (pivsR i)
  A++b≡piv i = appendLastLower (A i) (b i) (pivs i) (toℕ-pi≢n i)

  mPivotsR : MatrixPivots≁0 A pivsR
  proj₁ (mPivotsR i) = help $ mPivots i .proj₁
    where
    help : A++b i (pivs i) # 0# → _
    help rewrite A++b≡piv i = id
  proj₂ (mPivotsR i) j j<pI = help $ mPivots i .proj₂ (inject₁ j) (subst₂ ℕ._<_ (≡.sym (toℕ-inject₁ _)) (toℕ-pivR-≡ _) j<pI)
    where
    help : appendLast (A i) (b i) (inject₁ j) ≈ 0# → _
    help rewrite appendLastInj (A i) (b i) j = id

  allRowsR : AllRowsNormalized≁0 pivsR
  allRowsR = subst₂ ℕ._<_ (≡.sym $ toℕ-lower₁ _ $ toℕ-pi≢n _) (≡.sym $ toℕ-lower₁ _ $ toℕ-pi≢n _) ∘ pivsCrescent

  cols0R : ColumnsZero≁0 A pivsR
  cols0R i j i≢j = trans (sym (reflexive (appendLastLower (A _) (b _) _ (toℕ-pi≢n _)))) (columnsZero i j i≢j)

  pivs≁0 : PivsOne≁0 A pivsR
  pivs≁0 i = trans (sym (reflexive (A++b≡piv _))) (pivsOne i)

vecIn→vecBool : Vector (Fin n) m → Vector Bool n
vecIn→vecBool {m = ℕ.zero} xs i = false
vecIn→vecBool {m = ℕ.suc m} xs i with isYes (xs 0F F.≟ i)
... | true = true
... | false = vecIn→vecBool (tail xs) i

+-right : ∀ m p → m ℕ.+ ℕ.suc p ≡ ℕ.suc (m ℕ.+ p)
+-right ℕ.zero p = ≡.refl
+-right (ℕ.suc m) p rewrite +-right m p = ≡.refl

vecBool→×Vec : Vector Bool n → Σ[ m ∈ ℕ ] (Σ[ p ∈ ℕ ] (m ℕ.+ p ≡ n × Vector (Fin n) m × Vector (Fin n) p))
vecBool→×Vec {ℕ.zero} _ = _ , _ , ≡.refl , [] , []
vecBool→×Vec {ℕ.suc n} xs with xs 0F | vecBool→×Vec {n} (tail xs)
... | true  | m , p , m+p≡n , ys , zs = _ , _ , cong ℕ.suc m+p≡n , 0F ∷ F.suc ∘ ys , F.suc ∘ zs
... | false | m , p , m+p≡n , ys , zs = m , ℕ.suc p , ≡.trans (+-right _ _) (cong ℕ.suc m+p≡n) , F.suc ∘ ys , 0F ∷ F.suc ∘ zs

sameSizeVecBool : (xs : Vector (Fin n) m) → AllRowsNormalized≁0 xs → (let m′ , _ = vecBool→×Vec (vecIn→vecBool xs)) → m ≡ m′
sameSizeVecBool {ℕ.zero} {ℕ.zero} xs normed = ≡.refl
sameSizeVecBool {ℕ.zero} {ℕ.suc m} xs normed with () ← xs 0F
sameSizeVecBool {ℕ.suc n} {ℕ.zero} xs normed = {!proj₁ (vecBool→×Vec (tail (λ i → false)))!}
sameSizeVecBool {ℕ.suc n} {ℕ.suc m} xs normed = {!!}

vecIn→vecOut : (xs : Vector (Fin n) m) → AllRowsNormalized≁0 xs → ∃ (Vector (Fin n))
vecIn→vecOut {ℕ.zero} _ _ = _ , []
vecIn→vecOut {ℕ.suc n} {ℕ.zero} _ _ = _ , 0F ∷ F.suc ∘ proj₂ (vecIn→vecOut {n} [] p)
  where
  p : AllRowsNormalized≁0 []
  p {()}
vecIn→vecOut {ℕ.suc n} {ℕ.suc m} xs normed with xs 0F in eqXs
... | 0F = _ , F.suc ∘ proj₂ (vecIn→vecOut {n} (proj₂ ys) allRowsNormed)
  where
  ys : ∃ (Vector (Fin n))
  proj₁ ys = _
  proj₂ ys i = F.reduce≥ (tail xs i) (<.begin-strict
    0                <.≡˘⟨ cong toℕ eqXs ⟩
    toℕ (xs 0F)       <.<⟨ normed (ℕ.s≤s ℕ.z≤n) ⟩
    toℕ (xs (F.suc i)) <.∎)
    where module < = ≤-Reasoning

  allRowsNormed : AllRowsNormalized≁0 (proj₂ ys)
  allRowsNormed {x} {y} x<y = {!!}

... | suc c = {!!}


solveNormedEquation : ∀ (sx : SystemEquations n m) (open SystemEquations sx) → MatrixIsNormed≁0≈1 A →
  ∃ λ p → ∃ (IsFamilySolution {p = p})
solveNormedEquation {n} {m} sx ANormed = m ∸ n , vAffine , vAffFamily
  where
  open SystemEquations sx
  open MatrixIsNormed≁0≈1 ANormed

  vBool : Vector Bool m
  vBool = vecIn→vecBool pivs

  pivRes : Vector (Fin m) (m ∸ n)
  pivRes = {!!}

  vSplit : Vector (Fin (m ∸ n) ⊎ Fin n) m
  vSplit = {!!}

  vAffine : VecAffine m (m ∸ n)
  vAffine i with vSplit i
  ... | inj₁ j = vAff (δ j) 0#
  ... | inj₂ j  = vAff (λ k → - A j (pivRes k)) (b j)

  open Affine


  vAffFamily : IsFamilySolution vAffine
  vAffFamily vecs i = begin
    ∑ (λ j → A i j * (∑ (λ k → vecs k * coeff (vAffine j) k) + constant (vAffine j))) ≈⟨ {!!} ⟩
    ∑ (λ j → A i (pivs j) * (∑ (λ k → vecs k * coeff (vAffine (pivs j)) k) + constant (vAffine (pivs j)))) +
    ∑ (λ j → A i (pivRes j) * (∑ (λ k → vecs k * coeff (vAffine (pivRes j)) k) + constant (vAffine (pivRes j))))
      ≈⟨ +-cong ∑Piv ∑NPiv ⟩
    b i + ∑ (λ k → - (A i (pivRes k) * vecs k)) + ∑ (λ k → A i (pivRes k) * vecs k) ≈⟨ +-assoc (b i) _ _ ⟩
    b i + (∑ {m ∸ n} (λ k → - (A i (pivRes k) * vecs k)) + ∑ λ k → A i (pivRes k) * vecs k) ≈⟨ +-congˡ
      (begin
        _ ≈˘⟨ ∑Split _ (λ k → A i (pivRes k) * vecs k) ⟩
        _ ≈⟨ ∑Ext (λ k → -‿inverseˡ (A i (pivRes k) * vecs k)) ⟩
        ∑ {m ∸ n} (const 0#) ≈⟨ ∑0r (m ∸ n) ⟩
        _ ∎) ⟩
    b i + 0# ≈⟨ +-identityʳ _ ⟩
    b i ∎
    where

    AiPj≈δij : (i j : Fin n) → A i (pivs j) ≈ δ i j
    AiPj≈δij i j with i F.≟ j
    ... | yes ≡.refl = pivsOne _
    ... | no i≢j = columnsZero _ _ (i≢j ∘ ≡.sym)


    constVAffine≈ = {!!}

    ∑Piv = begin
      ∑ {n} (λ j → A i (pivs j) * (∑ (λ k → vecs k * coeff (vAffine (pivs j)) k) + constant (vAffine (pivs j))))
        ≈⟨ ∑Ext {n} (λ j → *-congʳ (AiPj≈δij i j)) ⟩
      ∑ (λ j → δ i j * (λ p → ∑ (λ k → vecs k * coeff (vAffine (pivs p)) k) + constant (vAffine (pivs p))) j )
        ≈⟨ ∑Mul1r {n} _ i ⟩
      ∑ (λ k → vecs k * coeff (vAffine (pivs i)) k) + constant (vAffine (pivs i))
        ≈⟨ +-cong {!!} constVAffine≈ ⟩
      ∑ (λ k → - (A i (pivRes k) * vecs k)) + b i ≈⟨ +-comm _ _ ⟩
      b i + ∑ (λ k → - (A i (pivRes k) * vecs k)) ∎

    ∑CoeffConst₁ : ∀ j k → coeff (vAffine (pivRes j)) k ≈ δ j k
    ∑CoeffConst₁ j k =  {!!}

    ∑CoeffConst₂ : ∀ j → constant (vAffine (pivRes j)) ≈ 0#
    ∑CoeffConst₂ j = {!!}

    ∑Eq = λ j → begin
      _ ≈⟨ +-identityʳ _ ⟩
      ∑ (λ k → vecs k * δ j k) ≈⟨ ∑Ext (λ k → *-comm (vecs k) _) ⟩
      ∑ (λ k → δ j k * vecs k) ≈⟨ ∑Mul1r _ j ⟩
      vecs j ∎

    ∑NPiv = begin
      ∑ (λ j → A i (pivRes j) * (∑ (λ k → vecs k * coeff (vAffine (pivRes j)) k) + constant (vAffine (pivRes j))))
        ≈⟨ ∑Ext (λ j → *-congˡ (+-cong (∑Ext (λ k → *-congˡ (∑CoeffConst₁ j k))) (∑CoeffConst₂ j))) ⟩
      ∑ (λ j → A i (pivRes j) * (∑ (λ k → vecs k * δ j k) + 0#)) ≈⟨ ∑Ext (λ j → *-congˡ (∑Eq j)) ⟩
      ∑ (λ j → A i (pivRes j) * vecs j) ∎
