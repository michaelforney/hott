{-# OPTIONS --without-K #-}
module HoTT.Homotopy where

open import Agda.Primitive
open import HoTT.Universe
open import HoTT.Identity

_~_ : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} (f g : (x : A) → P x) → 𝒰 (i ⊔ j)
_~_ {_} {_} {A} {_} f g = (x : A) → f x == g x

-- Lemma 2.4.2
~-refl : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j}
         (f : A → B) → f ~ f
~-refl f x = refl

~-sym : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j}
        (f g : A → B) → f ~ g → g ~ f
~-sym f g H x = (H x)⁻¹

~-trans : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j}
          (f g h : A → B) → f ~ g → g ~ h → f ~ h
~-trans f g h H₁ H₂ x = H₁ x ∙ H₂ x
