{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity.Pi

module HoTT.Sigma.Universal where

Σ-univ : ∀ {i j k} {X : 𝒰 i} {A : X → 𝒰 j} (P : (x : X) → A x → 𝒰 k) →
         ((x : X) → Σ (A x) λ a → P x a) ≃
         (Σ ((x : X) → A x) λ g → (x : X) → P x (g x))
Σ-univ _ = let open Iso in iso→eqv λ where
  .f h → pr₁ ∘ h , pr₂ ∘ h
  .g h x → pr₁ h x , pr₂ h x
  .η h → funext (Σ-uniq ∘ h)
  .ε h → Σ-uniq h
