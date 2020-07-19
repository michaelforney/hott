{-# OPTIONS --without-K #-}
module HoTT.Unit where

open import HoTT.Types

𝟏-rec : ∀ {i} (C : 𝒰 i) → C → 𝟏 → C
𝟏-rec C c ★ = c

𝟏-ind : ∀ {i} (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏) → C x
𝟏-ind C c ★ = c

𝟏-uniq : (x : 𝟏) → x == ★
𝟏-uniq ★ = refl
