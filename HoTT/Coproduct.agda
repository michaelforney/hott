module HoTT.Coproduct where

open import Agda.Primitive
open import HoTT.Universe

data _+_ {i j} (A : 𝒰 i) (B : 𝒰 j) : 𝒰 (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
      (C : 𝒰 k) → (A → C) → (B → C) → A + B → C
rec C g₀ g₁ (inl a) = g₀ a
rec C g₀ g₁ (inr b) = g₁ b

ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
      (C : A + B → 𝒰 k) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
ind C g₀ g₁ (inl a) = g₀ a
ind C g₀ g₁ (inr b) = g₁ b
