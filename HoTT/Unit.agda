module HoTT.Unit where

open import HoTT.Universe
open import HoTT.Identity hiding (ind)

record 𝟏 : 𝒰₀ where
  constructor ★

rec : ∀ {i} (C : 𝒰 i) → C → 𝟏 → C
rec C c ★ = c

ind : ∀ {i} (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏) → C x
ind C c ★ = c

upun : (x : 𝟏) → x == ★
upun ★ = refl
