module Vec.VecBool.Base where

open import Level using (Level)
open import Function
open import Data.Nat
open import Data.Vec as V
open import Data.Product
open import Data.Vec.Relation.Unary.Linked as L hiding (head)
import Data.Vec.Relation.Binary.Equality.Propositional as EProp
open import Data.Fin as F using (Fin)
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality hiding ([_])

private
  open module EProp′ {n} = EProp {A = Fin n}

private variable
  ℓ : Level
  m n p : ℕ

data VecBool : (m n : ℕ) → Set where
  []    : VecBool zero zero
  consF : VecBool m n → VecBool m (suc n)
  consT : VecBool m n → VecBool (suc m) (suc n)

IsNormed : (xs : Vec (Fin n) m) → Set
IsNormed = Linked F._<_

tailIsNormed′ : {xs : Vec (Fin (ℕ.suc n)) (suc m)} (0<xs : F.zero {suc m} F.< head xs) (isNormed : IsNormed xs)
  → (Vec (Fin n) (suc m))
tailIsNormed′ {m = zero} {xs = F.suc x ∷ xs} 0<xs isNormed = [ x ]
tailIsNormed′ {m = suc m} {xs = F.suc x ∷ xs} 0<xs (x<r ∷ isNormed) = x ∷ tailIsNormed′ (<-trans 0<xs x<r) isNormed

tailIsNormed : {xs : Vec (Fin (ℕ.suc n)) (suc m)} (0<xs : F.zero {suc m} F.< head xs) (isNormed : IsNormed xs)
  → Σ (Vec (Fin n) (suc m)) IsNormed
proj₁ (tailIsNormed 0<xs isNormed) = tailIsNormed′ 0<xs isNormed
proj₂ (tailIsNormed {m = zero} {F.suc x ∷ xs} 0<xs isNormed) = [-]
proj₂ (tailIsNormed {m = suc m} {F.suc x ∷ xs} 0<xs (x<r ∷ isNormed)) =
  help 0<xs x<r isNormed ∷ proj₂ (tailIsNormed (<-trans 0<xs x<r) isNormed)
  where
  help : ∀ {m} {xs} {x} (0<xs : (F.zero {m}) F.< F.suc x) (x<r  : F.suc x F.< head xs)
    (isNormed : Linked F._<_ xs)
    → x F.< head (tailIsNormed′ {m = m} {xs = xs} (<-trans 0<xs x<r) isNormed)
  help {zero} {F.suc y ∷ xs} {x} _ (s≤s x<r) isNormed = x<r
  help {suc m} {F.suc y ∷ xs} {x} _ (s≤s x<r) (_ ∷ isNormed) = x<r

sucTails : {xs : Vec (Fin (ℕ.suc n)) (suc m)} (0<xs : F.zero {suc m} F.< head xs) (isNormed : IsNormed xs)
  → V.map F.suc (tailIsNormed′ 0<xs isNormed) ≋ xs
sucTails {m = zero} {F.suc x ∷ []} 0<xs isNormed = ≡⇒≋ refl
sucTails {m = suc m} {F.suc x ∷ xs} 0<xs (x<r ∷ isNormed) = _∷_ {m} refl (sucTails (<-trans 0<xs x<r) isNormed)

isNormedPred′ : ∀ {xs : Vec (Fin (ℕ.suc n)) (suc m)} {x : Fin n} (isNormed : IsNormed (F.suc x ∷ xs))
  → Vec (Fin n) (suc m)
isNormedPred′ {m = zero} {xs = F.suc y ∷ xs} {x} (x<r ∷ isNormed) = [ y ]
isNormedPred′ {m = suc m} {xs = F.suc y ∷ xs} {x} (x<r ∷ isNormed) = y ∷ isNormedPred′ isNormed

sucNormPred : ∀ {xs : Vec (Fin (ℕ.suc n)) (suc m)} {x : Fin n} (x<y : F.suc x F.< head xs)
  (isNormed : IsNormed xs) → V.map F.suc (isNormedPred′ {m = m} {xs = xs} (x<y ∷ isNormed)) ≋ xs
sucNormPred {n} {zero} {F.suc x ∷ _} x<y [-] = _∷_ {n} refl ([] {n})
sucNormPred {n} {suc m} {F.suc x ∷ xs} x<y (x<r ∷ isNormed) = _∷_ {n} refl (sucNormPred _ isNormed)

isNormedPred : ∀ {xs : Vec (Fin (ℕ.suc n)) (suc m)} {x : Fin n} (isNormed : IsNormed (F.suc x ∷ xs))
  → Σ[ ys ∈ (Vec (Fin n) (suc m)) ] IsNormed (x ∷ ys)
proj₁ (isNormedPred isNormed) = isNormedPred′ isNormed
proj₂ (isNormedPred {m = zero} {F.suc y ∷ xs} {x} (s≤s x<r ∷ isNormed)) = x<r ∷ [-]
proj₂ (isNormedPred {m = suc m} {F.suc y ∷ xs} {x} (s≤s x<r ∷ isNormed)) = x<r ∷ proj₂ (isNormedPred isNormed)

toVBool : {xs : Vec (Fin n) m} (isNormed : IsNormed xs) → VecBool m n
toVBool {zero} {xs = []} [] = []
toVBool {suc n} {xs = []} [] = consF (toVBool [])
toVBool {suc n} {xs = 0F ∷ _} [-] = consT (toVBool [])
toVBool {suc n} {xs = F.suc x ∷ _} [-] = consF (toVBool {xs = x ∷ []} [-])
toVBool {suc n} {xs = 0F ∷ xs} (x<ys ∷ linked) = consT (toVBool (proj₂ (tailIsNormed x<ys linked)))
toVBool {2+ n} {xs = F.suc x ∷ xs} normed@(_∷_ {m} x<ys linked) =
  consF (toVBool (isNormedPred normed .proj₂))

vBool→vec : VecBool m n → Vec (Fin n) m
vBool→vec [] = []
vBool→vec (consT xs) = 0F ∷ V.map F.suc (vBool→vec xs)
vBool→vec (consF xs) = V.map F.suc (vBool→vec xs)

linkSuc : ∀ {xs : Vec (Fin n) m} → IsNormed xs → IsNormed (V.map F.suc xs)
linkSuc [] = []
linkSuc [-] = [-]
linkSuc (_∷_ {xs = y ∷ ys} x<y normed) = s<s x<y ∷ linkSuc normed

isNomedVBool : (xs : VecBool m n) → IsNormed (vBool→vec xs)
isNomedVBool [] = []
isNomedVBool (consT {zero} xs) with vBool→vec xs
... | [] = [-]
isNomedVBool (consT {suc m} xs) = help $ isNomedVBool xs
  where
  help : IsNormed (vBool→vec xs) → IsNormed (0F ∷ V.map F.suc (vBool→vec xs))
  help with vBool→vec xs
  ... | y ∷ ys = λ linked → s≤s z≤n ∷ linkSuc linked
isNomedVBool (consF xs) = linkSuc (isNomedVBool xs)

vFin→vecBool→vFin : {xs : Vec (Fin n) m} (isNormed : IsNormed xs) → vBool→vec (toVBool isNormed) ≋ xs
vFin→vecBool→vFin {zero} {xs = []} [] = [] {zero}
vFin→vecBool→vFin {suc n} {xs = []} [] rewrite ≋⇒≡ (vFin→vecBool→vFin {n} []) = [] {suc n}
vFin→vecBool→vFin {n} {xs = 0F ∷ .[]} [-] = _∷_ {n} refl (vFin→vecBool→vFin [])
vFin→vecBool→vFin {suc n} {xs = F.suc x ∷ .[]} [-]
  rewrite ≋⇒≡ (vFin→vecBool→vFin {xs = x ∷ []} [-]) = _∷_ {n} refl ([] {n})
vFin→vecBool→vFin {suc n} {xs = 0F ∷ xs} (_∷_ {m} x<ys normed) = _∷_ {n} refl
  (≋-trans (≡⇒≋ (cong (V.map F.suc) (≋⇒≡ (vFin→vecBool→vFin (proj₂ (tailIsNormed x<ys normed))))))
    (sucTails x<ys normed))
vFin→vecBool→vFin {2+ n} {xs = F.suc x ∷ xs} (x<ys ∷ normed) =
  ≋-trans (≡⇒≋ (cong (V.map F.suc) (≋⇒≡ (vFin→vecBool→vFin (isNormedPred (x<ys ∷ normed) .proj₂)))))
    (_∷_ {n} refl (sucNormPred _ normed))
