module HoTT.Coproduct where

open import HoTT.Types

rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
      (C : 𝒰 k) → (A → C) → (B → C) → A + B → C
rec C g₀ g₁ (inl a) = g₀ a
rec C g₀ g₁ (inr b) = g₁ b

ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
      (C : A + B → 𝒰 k) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
ind C g₀ g₁ (inl a) = g₀ a
ind C g₀ g₁ (inr b) = g₁ b
