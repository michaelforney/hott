{-# OPTIONS --without-K #-}
module HoTT.Boolean where

open import HoTT.Universe

data 𝟐 : 𝒰₀ where
  0₂ : 𝟐
  1₂ : 𝟐

rec : ∀ {i} (C : 𝒰 i) → C → C → 𝟐 → C
rec C c₀ c₁ 0₂ = c₀
rec C c₀ c₁ 1₂ = c₁

ind : ∀ {i} (C : 𝟐 → 𝒰 i) → C 0₂ → C 1₂ → (x : 𝟐) → C x
ind C c₀ c₁ 0₂ = c₀
ind C c₀ c₁ 1₂ = c₁
