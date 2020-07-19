{-# OPTIONS --without-K #-}
module HoTT.Equivalence.Proposition where

open import HoTT.Types
open import HoTT.Identity
open import HoTT.Equivalence
open import HoTT.Proposition
open import HoTT.Sigma.Identity
open import HoTT.Pi.Identity

-- Proven by Theorem 4.3.2
postulate
  isequiv-isProp : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {f : A → B} → isProp (isequiv f)
