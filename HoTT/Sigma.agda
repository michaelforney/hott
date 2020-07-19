{-# OPTIONS --without-K #-}
module HoTT.Sigma where

open import HoTT.Types

Σ-rec : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
        (C : 𝒰 k) → ((x : A) → B x → C) → (Σ A λ x → B x) → C
Σ-rec C g (a , b) = g a b

Σ-ind : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
        (C : Σ A B → 𝒰 k) → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
Σ-ind C g (a , b) = g a b

Σ-uniq : ∀ {i j} {A : 𝒰 i} {B : A → 𝒰 j}
         (x : Σ A B) → pr₁ x , pr₂ x == x
Σ-uniq = Σ-ind (λ x → pr₁ x , pr₂ x == x) (λ _ _ → refl)
