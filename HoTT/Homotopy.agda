{-# OPTIONS --without-K #-}
module HoTT.Homotopy where

open import HoTT.Types
open import HoTT.Identity

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
