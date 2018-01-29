module HoTT.NaturalNumber where

open import HoTT.Universe

data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

rec : ∀ {i} (C : 𝒰 i) → C → (ℕ → C → C) → ℕ → C
rec C c₀ cₛ 0 = c₀
rec C c₀ cₛ (succ n) = cₛ n (rec C c₀ cₛ n)

ind : ∀ {i} (C : ℕ → 𝒰 i) → C 0 → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
ind C c₀ cₛ 0 = c₀
ind C c₀ cₛ (succ n) = cₛ n (ind C c₀ cₛ n)
