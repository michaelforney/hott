{-# OPTIONS --without-K #-}
module HoTT.Sigma where

open import HoTT.Universe
open import Agda.Primitive

record Σ {i j} (A : 𝒰 i) (B : A → 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
infixr 15 _,_

rec : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
      (C : 𝒰 k) → ((x : A) → B x → C) → (Σ A λ x → B x) → C
rec C g (a , b) = g a b

ind : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
      (C : Σ A B → 𝒰 k) → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
ind C g (a , b) = g a b
