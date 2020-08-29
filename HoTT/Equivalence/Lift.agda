{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Equivalence.Lift where

open variables

Lift-equiv : Lift {i} A ≃ A
Lift-equiv = iso→eqv λ{.f → lower ; .g → lift ; .η _ → refl ; .ε _ → refl}
  where open Iso
