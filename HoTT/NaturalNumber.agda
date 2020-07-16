{-# OPTIONS --without-K #-}
module HoTT.NaturalNumber where

open import HoTT.Types

ℕ-rec : ∀ {i} (C : 𝒰 i) → C → (ℕ → C → C) → ℕ → C
ℕ-rec C c₀ cₛ 0 = c₀
ℕ-rec C c₀ cₛ (succ n) = cₛ n (ℕ-rec C c₀ cₛ n)

ℕ-ind : ∀ {i} (C : ℕ → 𝒰 i) → C 0 → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
ℕ-ind C c₀ cₛ 0 = c₀
ℕ-ind C c₀ cₛ (succ n) = cₛ n (ℕ-ind C c₀ cₛ n)

add : ℕ → ℕ → ℕ
add = ℕ-rec (ℕ → ℕ) id λ{_ g m → succ (g m)}
