{-# OPTIONS --without-K #-}
open import HoTT.Base

module HoTT.Transport.Coproduct where

private
  variable
    i : Level
    X : 𝒰 i
    A B : X → 𝒰 i
    x₁ x₂ : X

transport-+ : (p : x₁ == x₂) →
              transport (λ x → A x + B x) p ~
              +-rec (inl ∘ transport A p) (inr ∘ transport B p)
transport-+ refl (inl a) = refl
transport-+ refl (inr b) = refl
