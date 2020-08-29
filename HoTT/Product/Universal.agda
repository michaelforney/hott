{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity.Pi
open import HoTT.Identity.Product

module HoTT.Product.Universal where

×-univ : ∀ {i j k} {X : 𝒰 i} (A : X → 𝒰 j) (B : X → 𝒰 k) →
         ((c : X) → A c × B c) ≃ Π X A × Π X B
×-univ {X = X} A B = let open Iso in iso→eqv λ where
  .f f → pr₁ ∘ f , pr₂ ∘ f
  .g f x → pr₁ f x , pr₂ f x
  .η f → funext (×-uniq ∘ f)
  .ε f → ×-pair⁼ (refl , refl)
