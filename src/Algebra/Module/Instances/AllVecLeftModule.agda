open import Function using (_$_)
open import Algebra.Bundles

module Algebra.Module.Instances.AllVecLeftModule
  {c ℓ} (ring : Ring c ℓ) where

open import Data.Nat using (ℕ)
open import Data.Vec.Functional
open import Data.Product
open import Vector.Structures

open import Algebra.Core
open import Algebra.Module
open import Algebra.Structures
open import Algebra.Module.Instances.FunctionalVector ring
  using (_+ᴹ_; -ᴹ_; -ᴹ‿cong; -ᴹ‿inverse; +ᴹ-comm; isMonoid)
import Algebra.Module.Definitions.Left as DLeft′

open Ring ring
open VRing rawRing renaming (0ⱽ to 𝟙)

open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open module DLeft {n} = DLeft′ (Vector Carrier n) (_≋_ {n})

private variable
  n : ℕ


_*ₗ_ : Op₂ $ Vector Carrier n
_*ₗ_ = _*ⱽ_

𝟘 : Vector Carrier n
𝟘 _ = 0#

*ₗ-cong : Congruent _≋_ (_*ₗ_ {n})
*ₗ-cong x≈y u≈v i = *-cong (x≈y i) (u≈v i)

*ₗ-zeroˡ : LeftZero {n = n} 𝟘 𝟘 _*ₗ_
*ₗ-zeroˡ xs i = zeroˡ (xs i)

*ₗ-distribʳ : _*ₗ_ DistributesOverʳ _+ᴹ_ ⟶ _+ᴹ_ {n}
*ₗ-distribʳ xs m n i = distribʳ _ _ _

*ₗ-identityˡ : LeftIdentity 𝟙 (_*ₗ_ {n})
*ₗ-identityˡ xs i = *-identityˡ (xs i)

*ₗ-assoc : Associative _*ₗ_ (_*ₗ_ {n})
*ₗ-assoc m n xs i = *-assoc _ _ _

*ₗ-zeroʳ : RightZero (𝟘 {n}) _*ₗ_
*ₗ-zeroʳ m _ = zeroʳ _

*ₗ-distribˡ : _*ₗ_ DistributesOverˡ (_+ᴹ_ {n})
*ₗ-distribˡ m xs ys i = distribˡ _ _ _

+ᴹ-isCommutativeMonoid : IsCommutativeMonoid (_≋_ {n}) _+ᴹ_ 𝟘
+ᴹ-isCommutativeMonoid = record
  { isMonoid = record { isSemigroup =
  record { isMagma = record
      { isEquivalence = record { refl = λ i → refl
                              ; sym = λ x i → sym (x i)
                              ; trans = λ a b i → trans (a i) (b i) }
      ; ∙-cong = λ a b i → +-cong (a i) (b i)
      }
  ; assoc = λ x y z i → +-assoc _ _ _ }
  ; identity = (λ x i → +-identityˡ _) , λ x i → +-identityʳ _ }
  ; comm     = λ x y i → +-comm _ _
  }


v-isSemiWAZ : IsSemiringWithoutAnnihilatingZero (_≋_ {n}) _+ᴹ_ _*ⱽ_ 𝟘 𝟙
v-isSemiWAZ = record
               { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
               ; *-cong = *ₗ-cong
               ; *-assoc = *ₗ-assoc
               ; *-identity = *ₗ-identityˡ , (λ _ _ → *-identityʳ _)
               ; distrib = *ₗ-distribˡ , (λ x y z i → distribʳ _ _ _)
               }

v-isSemiring : IsSemiring (_≋_ {n}) _+ᴹ_ _*ⱽ_ 𝟘 𝟙
v-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = v-isSemiWAZ
  ; zero = *ₗ-zeroˡ , *ₗ-zeroʳ
  }

v-semiring : (n : ℕ) → Semiring _ _
v-semiring n = record { isSemiring = v-isSemiring {n} }

v-isRing : IsRing (_≋_ {n}) _+ᴹ_ _*ⱽ_ -ᴹ_ 𝟘 𝟙
v-isRing = record
  { +-isAbelianGroup = record
    { isGroup = record
      { isMonoid = isMonoid
      ; inverse = -ᴹ‿inverse
      ; ⁻¹-cong = -ᴹ‿cong
      }
    ; comm = +ᴹ-comm
    }
  ; *-cong = *ₗ-cong
  ; *-assoc = *ₗ-assoc
  ; *-identity = *ₗ-identityˡ , (λ _ _ → *-identityʳ _)
  ; distrib = *ₗ-distribˡ , (λ x y z i → distribʳ _ _ _)
  }


v-ring : (n : ℕ) → Ring _ _
v-ring n = record { isRing = v-isRing {n} }

isPreleftSemimodule : IsPreleftSemimodule (v-semiring n) _≋_ _+ᴹ_ 𝟘 _*ₗ_
isPreleftSemimodule = record
  { *ₗ-cong = *ₗ-cong
  ; *ₗ-zeroˡ = *ₗ-zeroˡ
  ; *ₗ-distribʳ = *ₗ-distribʳ
  ; *ₗ-identityˡ = *ₗ-identityˡ
  ; *ₗ-assoc = *ₗ-assoc
  ; *ₗ-zeroʳ = *ₗ-zeroʳ
  ; *ₗ-distribˡ = *ₗ-distribˡ
  }

isLeftSemimodule : IsLeftSemimodule (v-semiring n) _≋_ _+ᴹ_ 𝟘 _*ₗ_
isLeftSemimodule = record
  { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
  ; isPreleftSemimodule    = isPreleftSemimodule
  }

isLeftModule : IsLeftModule (v-ring n) _≋_ _+ᴹ_ 𝟘 -ᴹ_ _*ₗ_
isLeftModule = record
  { isLeftSemimodule = isLeftSemimodule
  ; -ᴹ‿cong = -ᴹ‿cong
  ; -ᴹ‿inverse = -ᴹ‿inverse
  }

leftModule : (n : ℕ) → LeftModule (v-ring n) _ _
leftModule n = record { isLeftModule = isLeftModule }
