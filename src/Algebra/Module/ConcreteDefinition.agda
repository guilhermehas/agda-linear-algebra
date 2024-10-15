open import Algebra
open import Algebra.Apartness
open import Algebra.DecidableField

module Algebra.Module.ConcreteDefinition {c ℓ₁} (HCR : DecidableField c ℓ₁ ℓ₁) where

open import Level
open import Function
open import Data.Nat hiding (_+_; _*_; _⊔_; _≟_)
open import Data.Fin using () renaming (suc to fsuc)
open import Data.Empty.Polymorphic
open import Data.Product
open import Data.Unit.Polymorphic hiding (_≟_)
import Data.Vec as V
open import Data.Vec.Functional
open import Data.Fin.Patterns
open import Algebra.Matrix.Structures
open import Relation.Nullary.Negation.Core

open DecidableField HCR renaming (Carrier to A;  trans to infixr 5 _∙_)
open import Algebra.DecidableField.Properties HCR
open import Algebra.Module.Instances.FunctionalVector ring
import Algebra.Module.DefsField as MDef'
open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Nullary

open module MDef {n} = MDef' heytingField (leftModule n)

open MRing rawRing hiding (0ᴹ)

private variable
  m n : ℕ
  xs ys : Vector A n


AreCollinear : (xs ys : Vector A n) → Set ℓ₁
AreCollinear {0} xs ys = ⊥
AreCollinear {1} xs ys = ⊤
AreCollinear {2} xs ys = xs 0F * ys 1F ≈ xs 1F * ys 0F
AreCollinear {2+ (suc n)} xs ys = xs 0F * ys 1F ≈ xs 1F * ys 0F × AreCollinear (tail xs) (tail ys)

AreNotCollinear : (xs ys : Vector A n) → Set ℓ₁
AreNotCollinear {0} xs ys = ⊤
AreNotCollinear {1} xs ys = ⊥
AreNotCollinear {2+ n} xs ys = AreCollinear (tail xs) (tail ys) → xs 0F * ys 1F # xs 1F * ys 0F

AreCollinear⇒LinDep : AreCollinear xs ys → IsLinearDependent (xs ∷ ys ∷ [])
AreCollinear⇒LinDep {1} {xs} {ys} _ with ys 0F #≟ 0#
... | diff ys0F#0 _ = help₁ , 0F , ys0F#0
  where
  help = begin
      ys 0F * xs 0F + (- xs 0F * ys 0F + 0#) ≈⟨ +-congˡ (+-identityʳ _ ∙ sym (-‿distribˡ-* _ _) ∙ -‿cong (*-comm _ _)) ⟩
      ys 0F * xs 0F + - (ys 0F * xs 0F)      ≈⟨ -‿inverseʳ _ ⟩
      0# ∎
  help₁ : _
  help₁ = fromVec (ys 0F V.∷ V.[ - xs 0F ]) by λ where 0F → help
... | sameIE ys0F≈0 ¬# = help₁ , 1F , 1#0
  where
  help = begin
    0# * xs 0F + (1# * ys 0F + 0#) ≈⟨ +-cong (zeroˡ _) (+-congʳ (*-identityˡ _) ∙ +-identityʳ _) ⟩
    0# + ys 0F                     ≈⟨ +-identityˡ _ ⟩
    ys 0F                          ≈⟨ ys0F≈0 ⟩
    0# ∎

  help₁ = fromVec (0# V.∷ V.[ 1# ]) by λ where 0F → help
AreCollinear⇒LinDep {2} {xs} {ys} same with ys 0F #≟ 0#
... | diff x#y ¬≈ = help₁ , 0F , x#y
  where
  help = begin
      ys 0F * xs 0F + (- xs 0F * ys 0F + 0#) ≈⟨ +-congˡ (+-identityʳ _ ∙ sym (-‿distribˡ-* _ _) ∙ -‿cong (*-comm _ _)) ⟩
      ys 0F * xs 0F + - (ys 0F * xs 0F)      ≈⟨ -‿inverseʳ _ ⟩
      0# ∎

  help₃ = begin
      ys 0F * xs 1F + (- xs 0F * ys 1F + 0#) ≈⟨ +-cong (*-comm _ _ ∙ sym same) (+-identityʳ _ ∙ sym (-‿distribˡ-* _ _)) ⟩
      xs 0F * ys 1F + - (xs 0F * ys 1F)      ≈⟨ -‿inverseʳ _ ⟩
      0# ∎

  help₂ : _
  help₂ 0F = help
  help₂ 1F = help₃

  help₁ : _
  help₁ = fromVec (ys 0F V.∷ V.[ - xs 0F ]) by help₂
... | sameIE ys0F≈0 _ with ys 1F #≟ 0#
... | diff ys1F#0 _ = help₁ , 0F , ys1F#0
  where
  help = begin
      ys 1F * xs 0F + (- xs 1F * ys 0F + 0#) ≈⟨ +-cong (*-comm _ _ ∙ same) (+-identityʳ _ ∙ sym (-‿distribˡ-* _ _)) ⟩
      xs 1F * ys 0F + - (xs 1F * ys 0F)      ≈⟨ -‿inverseʳ _ ⟩
      0# ∎

  help₃ = begin
      ys 1F * xs 1F + (- xs 1F * ys 1F + 0#) ≈⟨ +-cong (*-comm _ _) (+-identityʳ _ ∙ sym (-‿distribˡ-* _ _)) ⟩
      xs 1F * ys 1F + - (xs 1F * ys 1F)      ≈⟨ -‿inverseʳ _ ⟩
      0# ∎

  help₂ : _
  help₂ 0F = help
  help₂ 1F = help₃

  help₁ : _
  help₁ = fromVec (ys 1F V.∷ V.[ - xs 1F ]) by help₂
... | sameIE ys1F≈0 _ = help₁ , 1F , 1#0
  where
  help = begin
    0# * xs 0F + (1# * ys 0F + 0#) ≈⟨ +-cong (zeroˡ _) (+-congʳ (*-identityˡ _) ∙ +-identityʳ _) ⟩
    0# + ys 0F                     ≈⟨ +-identityˡ _ ⟩
    ys 0F                          ≈⟨ ys0F≈0 ⟩
    0# ∎

  help₃ = begin
    0# * xs 1F + (1# * ys 1F + 0#) ≈⟨ +-cong (zeroˡ _) (+-congʳ (*-identityˡ _) ∙ +-identityʳ _) ⟩
    0# + ys 1F                     ≈⟨ +-identityˡ _ ⟩
    ys 1F                          ≈⟨ ys1F≈0 ⟩
    0# ∎

  help₂ : _
  help₂ 0F = help
  help₂ 1F = help₃

  help₁ = fromVec (0# V.∷ V.[ 1# ]) by help₂

AreCollinear⇒LinDep {2+ (ℕ.suc n)} {xs} {ys} (same , col) =
  let linRest = AreCollinear⇒LinDep {xs = tail xs} col in
  {!!}

IsCLinearIndependent : Matrix A n m → m ≤ 3 → Set ℓ₁
IsCLinearIndependent {0} {0} xs z≤n = ⊤
IsCLinearIndependent {suc n} {0} xs z≤n = ⊥
IsCLinearIndependent {0} {1} xs (s≤s z≤n) = ⊤
IsCLinearIndependent {1} {1} xs (s≤s z≤n) = xs 0F 0F # 0#
IsCLinearIndependent {2+ _} {1} xs (s≤s z≤n) = ⊥
IsCLinearIndependent {0} {2} xs (s≤s (s≤s z≤n)) = ⊤
IsCLinearIndependent {1} {2} xs (s≤s (s≤s z≤n)) = xs 0F 0F # 0#
IsCLinearIndependent {2} {2} xs (s≤s (s≤s z≤n)) = xs 0F 0F * xs 1F 1F # xs 0F 1F * xs 1F 0F
IsCLinearIndependent {2+ (suc _)} {2} xs (s≤s (s≤s z≤n)) = ⊥
IsCLinearIndependent {0} {3} xs (s≤s (s≤s (s≤s z≤n))) = ⊤
IsCLinearIndependent {1} {3} xs (s≤s (s≤s (s≤s z≤n))) = xs 0F 0F # 0#
IsCLinearIndependent {2} {3} xs (s≤s (s≤s (s≤s z≤n))) = AreNotCollinear (xs 0F) (xs 1F)
IsCLinearIndependent {3} {3} xs (s≤s (s≤s (s≤s z≤n))) = let
  -- Determinant different than zero
  -- TODO: rename to a to a00, ...
  a = xs 0F 0F; b = xs 0F 1F; c = xs 0F 2F
  d = xs 1F 0F; e = xs 1F 0F; f = xs 1F 2F
  g = xs 2F 0F; h = xs 2F 0F; i = xs 2F 2F
  in a * (e * i - h * f) + b * (g * f - d * i) + c * (d * h - e * g) # 0#
  -- xs 0F ⋆ᵣ (xs 1F × xs 2F)
IsCLinearIndependent {2+ (2+ n)} {3} xs (s≤s (s≤s (s≤s z≤n))) = ⊥

Ind⇒IsCInd : (xs : Matrix A n m) (m≤3 : m ≤ 3) → IsLinearIndependent xs → IsCLinearIndependent xs m≤3
Ind⇒IsCInd = {!!}

IsCInd⇒Ind : (xs : Matrix A n m) (m≤3 : m ≤ 3) → IsCLinearIndependent xs m≤3 → IsLinearIndependent xs
IsCInd⇒Ind {1} {1} xs (s≤s z≤n) cLin ∑≈0 0F =
  x#0*y≈0⇒y≈0 cLin (*-comm _ _ ∙ (sym (+-identityʳ _) ∙ ∑≈0 0F))
IsCInd⇒Ind {1} {2} xs (s≤s (s≤s z≤n)) cLin ∑≈0 0F =
  x#0*y≈0⇒y≈0 cLin (*-comm _ _ ∙ (sym (+-identityʳ _) ∙ (∑≈0 0F)))
IsCInd⇒Ind {2} {2} xs (s≤s (s≤s z≤n)) cLin {ys} ∑≈0 0F = {!!}
  where
  open *-solver

  help₁ = begin
    ys 0F * (xs 1F 1F * xs 0F 0F) + ys 1F * xs 1F 0F * xs 1F 1F
      ≈⟨ +-cong (solve 3 (λ a b c → c ⊕ (a ⊕ b) , a ⊕ (c ⊕ b)) refl _ _ _)
                (solve 3 (λ a b c → a ⊕ b ⊕ c , c ⊕ (a ⊕ b)) refl _ _ _) ⟩
    xs 1F 1F * (ys 0F * xs 0F 0F) + xs 1F 1F * (ys 1F * xs 1F 0F) ≈˘⟨ distribˡ _ _ _ ⟩
    xs 1F 1F * (ys 0F * xs 0F 0F + ys 1F * xs 1F 0F)
      ≈⟨ *-congˡ {x = xs 1F 1F} (sym (+-congˡ (+-identityʳ _)) ∙ ∑≈0 0F) ⟩
    _ * 0# ≈⟨ zeroʳ _ ⟩
    0# ∎

  help₂ = begin
    ys 0F * (xs 1F 0F * xs 0F 1F) + ys 1F * xs 1F 0F * xs 1F 1F ≈⟨ +-cong
      (solve 3 (λ a b c → b ⊕ (a ⊕ c) , a ⊕ (b ⊕ c)) refl _ _ _)
      (solve 3 (λ a b c → b ⊕ a ⊕ c   , a ⊕ (b ⊕ c)) refl _ _ _) ⟩
    xs 1F 0F * (ys 0F * xs 0F 1F) + xs 1F 0F * (ys 1F * xs 1F 1F) ≈˘⟨ distribˡ _ _ _ ⟩
    xs 1F 0F * (ys 0F * xs 0F 1F + ys 1F * xs 1F 1F)
      ≈⟨ *-congˡ (sym (+-congˡ (+-identityʳ _)) ∙ ∑≈0 1F) ⟩
    _ * 0# ≈⟨ zeroʳ _ ⟩
    0# ∎

  help₃ = begin
    ys 0F * (xs 1F 1F * xs 0F 0F) + ys 1F * xs 1F 0F * xs 1F 1F ≈⟨ help₁ ⟩
    0# ≈˘⟨ help₂ ⟩
    ys 0F * (xs 1F 0F * xs 0F 1F) + ys 1F * xs 1F 0F * xs 1F 1F ∎

  help₄ : ys 0F * (xs 1F 1F * xs 0F 0F) ≈ ys 0F * (xs 1F 0F * xs 0F 1F)
  help₄ = +-cancelʳ _ _ _ help₃

IsCInd⇒Ind {2} {2} xs (s≤s (s≤s z≤n)) cLin ∑≈0 1F = {!!}

IsCInd⇒Ind {1} {3} xs (s≤s (s≤s (s≤s z≤n))) cLin ∑≈0 0F =
  x#0*y≈0⇒y≈0 cLin (*-comm _ _ ∙ (sym (+-identityʳ _) ∙ ∑≈0 0F))
IsCInd⇒Ind {2} {3} xs (s≤s (s≤s (s≤s z≤n))) cLin ∑≈0 i = {!!}
IsCInd⇒Ind {3} {3} xs (s≤s (s≤s (s≤s z≤n))) cLin ∑≈0 i = {!!}
