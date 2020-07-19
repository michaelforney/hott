{-# OPTIONS --without-K #-}
module HoTT.Proposition where

open import HoTT.Types

isProp : ∀ {i} → 𝒰 i → 𝒰 i
isProp P = (x y : P) → x == y
