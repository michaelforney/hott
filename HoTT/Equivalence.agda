{-# OPTIONS --without-K #-}
module HoTT.Equivalence where

open import HoTT.Types
open import HoTT.Identity
open import HoTT.Homotopy

qinv→isequiv : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {f : A → B} → qinv f → isequiv f
qinv→isequiv (g , α , β) = (g , α) , (g , β)

isequiv→qinv : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {f : A → B} → isequiv f → qinv f
isequiv→qinv {f = f} ((g , α) , (h , β)) = g , α , β'
  where
    γ : g ~ h
    γ x = (β (g x))⁻¹ ∙ ap h (α x)
    β' : g ∘ f ~ id
    β' x = γ (f x) ∙ β x

-- Lemma 2.4.12
--  (i)
≃-refl : ∀ {i} {A : 𝒰 i} → A ≃ A
≃-refl = id , (id , λ x → refl) , (id , λ x → refl)
--  (ii)
≃-sym : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A ≃ B → B ≃ A
≃-sym (f , e) with isequiv→qinv e
... | g , α , β = g , (f , β) , (f , α)
--  (iii)
≃-trans : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} → A ≃ B → B ≃ C → A ≃ C
≃-trans (f₁ , e₁) (f₂ , e₂) with isequiv→qinv e₁ | isequiv→qinv e₂
... | g₁ , α₁ , β₁ | g₂ , α₂ , β₂ = (f₂ ∘ f₁) , qinv→isequiv (g₁ ∘ g₂ , α , β)
  where
    α : f₂ ∘ f₁ ∘ g₁ ∘ g₂ ~ id
    α x = ap f₂ (α₁ (g₂ x)) ∙ α₂ x
    β : g₁ ∘ g₂ ∘ f₂ ∘ f₁ ~ id
    β x = ap g₁ (β₂ (f₁ x)) ∙ β₁ x
