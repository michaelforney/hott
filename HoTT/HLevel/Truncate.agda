{-# OPTIONS --without-K --rewriting #-}
open import HoTT.Base
open import HoTT.HLevel

module HoTT.HLevel.Truncate where

open variables

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set a
{-# BUILTIN REWRITE _↦_ #-}

postulate
  ∥_∥ : 𝒰 i → 𝒰 i
  ∣_∣ : A → ∥ A ∥
  instance ∥-hlevel : hlevel 1 ∥ A ∥
  ∥-rec : ⦃ hlevel 1 B ⦄ → (A → B) → ∥ A ∥ → B
  ∥-β : ⦃ _ : hlevel 1 B ⦄ → (f : A → B) (x : A) → ∥-rec f ∣ x ∣ ↦ f x
{-# REWRITE ∥-β #-}

{-
  data Squash (A : 𝒰 i) : 𝒰 i where
    squash : A → Squash A

∥_∥ : 𝒰 i → 𝒰 i
∥_∥ = Squash

∣_∣ : A → ∥ A ∥
∣_∣ = squash

postulate instance ∥-hlevel : hlevel 1 ∥ A ∥

∥-rec : {B : 𝒰 i} → ⦃ hlevel 1 B ⦄ → (A → B) → ∥ A ∥ → B
∥-rec f (squash x) = f x
-}
