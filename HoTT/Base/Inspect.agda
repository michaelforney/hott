{-# OPTIONS --without-K #-}
open import HoTT.Base

module HoTT.Base.Inspect where

open variables

data Inspect {i j} {A : 𝒰 i} {P : A → 𝒰 j} (f : Π A P) (x : A) (y : P x) : 𝒰 (i ⊔ j) where
  [_] : y == f x → Inspect f x y

inspect : (f : Π A P) (x : A) → Inspect f x (f x)
inspect f x = [ refl ]
