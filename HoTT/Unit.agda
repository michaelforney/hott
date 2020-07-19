{-# OPTIONS --without-K #-}
module HoTT.Unit where

open import HoTT.Types
open import HoTT.Equivalence

𝟏-rec : ∀ {i} (C : 𝒰 i) → C → 𝟏 → C
𝟏-rec C c ★ = c

𝟏-ind : ∀ {i} (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏) → C x
𝟏-ind C c ★ = c

𝟏-uniq : (x : 𝟏) → x == ★
𝟏-uniq ★ = refl

𝟏-identity : {x y : 𝟏} → (x == y) ≃ 𝟏
𝟏-identity = f , qinv→isequiv (g , α , β)
  where
    f : {x y : 𝟏} → x == y → 𝟏
    f _ = ★
    g : {x y : 𝟏} → 𝟏 → x == y
    g {★} {★} _ = refl
    α : f ∘ g ~ id
    α ★ = refl
    β : g ∘ f ~ id
    β refl = refl
