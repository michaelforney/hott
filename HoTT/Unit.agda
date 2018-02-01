{-# OPTIONS --without-K #-}
module HoTT.Unit where

open import HoTT.Types

rec : ∀ {i} (C : 𝒰 i) → C → 𝟏 → C
rec C c ★ = c

ind : ∀ {i} (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏) → C x
ind C c ★ = c

upun : (x : 𝟏) → x == ★
upun ★ = refl
