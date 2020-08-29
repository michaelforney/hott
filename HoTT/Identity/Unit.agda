{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Identity.Unit where

open variables

=𝟏-equiv : {x y : 𝟏 {i}} → (x == y) ≃ 𝟏 {j}
=𝟏-equiv {i} {j} {★} {★} = f , qinv→isequiv (g , η , ε)
  where
    f : {x y : 𝟏} → x == y → 𝟏 {j}
    f _ = ★
    g : {x y : 𝟏} → 𝟏 {j} → x == y
    g {★} {★} _ = refl
    η : g ∘ f ~ id
    η refl = refl
    ε : f ∘ g {★} {★} ~ id
    ε ★ = refl
