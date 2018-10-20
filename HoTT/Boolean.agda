{-# OPTIONS --without-K #-}
module HoTT.Boolean where

open import HoTT.Types

𝟐-rec : ∀ {i} (C : 𝒰 i) → C → C → 𝟐 → C
𝟐-rec C c₀ c₁ 0₂ = c₀
𝟐-rec C c₀ c₁ 1₂ = c₁

𝟐-ind : ∀ {i} (C : 𝟐 → 𝒰 i) → C 0₂ → C 1₂ → (x : 𝟐) → C x
𝟐-ind C c₀ c₁ 0₂ = c₀
𝟐-ind C c₀ c₁ 1₂ = c₁
