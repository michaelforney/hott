{-# OPTIONS --without-K #-}
module HoTT.Unit where

open import HoTT.Types
open import HoTT.Equivalence

rec : ∀ {i} (C : 𝒰 i) → C → 𝟏 → C
rec C c ★ = c

ind : ∀ {i} (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏) → C x
ind C c ★ = c

upun : (x : 𝟏) → x == ★
upun ★ = refl

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
