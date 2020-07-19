{-# OPTIONS --without-K #-}
module HoTT.Unit.Identity where

open import HoTT.Types
open import HoTT.Equivalence

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
