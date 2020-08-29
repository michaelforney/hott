{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity

module HoTT.Transport.Identity where

open variables

unitₗᵣ : {x y : A} {p : x == y} → p == refl ∙ p ∙ refl
unitₗᵣ {p = refl} = refl

-- Theorem 2.11.3
transport= : {a a' : A} (f g : A → B) (p : a == a') (q : f a == g a) →
             transport (λ x → f x == g x) p q == ap f p ⁻¹ ∙ q ∙ ap g p
transport= _ _ refl _ = unitₗᵣ

transport=-id-const : (a : A) {x₁ x₂ : A} (p : x₁ == x₂) (q : x₁ == a) →
                      transport (λ x → x == a) p q == p ⁻¹ ∙ q
transport=-id-const _ refl refl = refl

transport=-const-id : {x₁ x₂ : A} (p : x₁ == x₂) (a : A) (q : a == x₁) →
                      transport (λ x → a == x) p q == q ∙ p
transport=-const-id refl _ refl = refl

transport=-id-id : {x₁ x₂ : A} (p : x₁ == x₂) (q : x₁ == x₁) →
                   transport (λ x → x == x) p q == p ⁻¹ ∙ q ∙ p
transport=-id-id refl _ = unitₗᵣ

transport=-constₗ : (b : B) (f : A → B) {x₁ x₂ : A} (p : x₁ == x₂) (q : b == f x₁) →
                    transport (λ x → b == f x) p q == q ∙ ap f p
transport=-constₗ _ _ refl _ = unitᵣ

transport=-constᵣ : (f : A → B) (b : B) {x₁ x₂ : A} (p : x₁ == x₂) (q : f x₁ == b) →
                    transport (λ x → f x == b) p q == ap f p ⁻¹ ∙ q
transport=-constᵣ _ _ refl refl = refl

transport=-idₗ : (f : A → A) {x₁ x₂ : A} (p : x₁ == x₂) (q : x₁ == f x₁) →
                 transport (λ x → x == f x) p q == p ⁻¹ ∙ q ∙ ap f p
transport=-idₗ _ refl _ = unitₗᵣ

transport=-idᵣ : (f : A → A) {x₁ x₂ : A} (p : x₁ == x₂) (q : f x₁ == x₁) →
                 transport (λ x → f x == x) p q == ap f p ⁻¹ ∙ q ∙ p
transport=-idᵣ _ refl _ = unitₗᵣ
