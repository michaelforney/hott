{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Equivalence.Coproduct where

open variables
private variable A' B' : 𝒰 i

+-empty₁ : 𝟎 {i} + B ≃ B
+-empty₁ = let open Iso in iso→eqv λ where
  .f (inl ())
  .f (inr b) → b
  .g         → inr
  .η (inl ())
  .η (inr b) → refl
  .ε _       → refl

+-empty₂ : A + 𝟎 {j} ≃ A
+-empty₂ = let open Iso in iso→eqv λ where
  .f (inl a) → a
  .f (inr ())
  .g         → inl
  .η (inl b) → refl
  .η (inr ())
  .ε _       → refl

+-comm : A + B ≃ B + A
+-comm = let open Iso in iso→eqv λ where
  .f (inl a) → inr a
  .f (inr b) → inl b
  .g (inl b) → inr b
  .g (inr a) → inl a
  .η (inl a) → refl
  .η (inr b) → refl
  .ε (inl b) → refl
  .ε (inr a) → refl

+-equiv : A ≃ A' → B ≃ B' → A + B ≃ A' + B'
+-equiv e₁ e₂ =
  iso→eqv λ where
    .f (inl a)  → inl (f₁ a)
    .f (inr b)  → inr (f₂ b)
    .g (inl a') → inl (g₁ a')
    .g (inr b') → inr (g₂ b')
    .η (inl a)  → ap inl (η₁ a)
    .η (inr b)  → ap inr (η₂ b)
    .ε (inl a') → ap inl (ε₁ a')
    .ε (inr b') → ap inr (ε₂ b')
  where
  open Iso
  open Iso (eqv→iso e₁) renaming (f to f₁ ; g to g₁ ; η to η₁ ; ε to ε₁)
  open Iso (eqv→iso e₂) renaming (f to f₂ ; g to g₂ ; η to η₂ ; ε to ε₂)
