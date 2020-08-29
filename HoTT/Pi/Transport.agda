{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity.Sigma

module HoTT.Pi.Transport where

transport-→ : ∀ {i j k} {X : 𝒰 i} (A : X → 𝒰 j) (B : X → 𝒰 k)
              {x₁ x₂ : X} (p : x₁ == x₂) (f : A x₁ → B x₁) →
              transport (λ x → A x → B x) p f == transport B p ∘ f ∘ transport A (p ⁻¹)
transport-→ A B refl f = refl

module _ {i j k} {X : 𝒰 i} (A : X → 𝒰 j) (B : {x : X} → A x → 𝒰 k)
         {x₁ x₂ : X} (p : x₁ == x₂) (f : Π[ a ∶ A x₁ ] B a) (a : A x₂)
  where
  private
    B̂ : Σ[ x ∶ X ] A x → 𝒰 k
    B̂ w = B (pr₂ w)
  transport-Π : transport (λ x → Π[ a ∶ A x ] B a) p f a ==
                transport {x = x₁ , transport _ (p ⁻¹) a} {y = x₂ , a}
                  B̂ (pair⁼ (p ⁻¹ , refl) ⁻¹) (f (transport A (p ⁻¹) a))
  transport-Π rewrite p = refl
