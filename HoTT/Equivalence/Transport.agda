{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Equivalence.Transport where

open variables

transport-equiv : {x y : A} → x == y → P x ≃ P y
transport-equiv {A = A} {P = P} p = f , qinv→isequiv (g , η p , ε p)
  where
  f = transport P p
  g = transport P (p ⁻¹)
  variable x y : A
  η : (p : x == y) → transport P (p ⁻¹) ∘ transport P p ~ id
  η refl _ = refl
  ε : (p : x == y) → transport P p ∘ transport P (p ⁻¹) ~ id
  ε refl _ = refl
