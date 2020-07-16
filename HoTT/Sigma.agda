{-# OPTIONS --without-K #-}
module HoTT.Sigma where

open import HoTT.Types
open import HoTT.Equivalence
open import HoTT.Identity

Σ-rec : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
        (C : 𝒰 k) → ((x : A) → B x → C) → (Σ A λ x → B x) → C
Σ-rec C g (a , b) = g a b

Σ-ind : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} →
        (C : Σ A B → 𝒰 k) → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
Σ-ind C g (a , b) = g a b

Σ-up : ∀ {i j} {A : 𝒰 i} {B : A → 𝒰 j}
         (x : Σ A B) → pr₁ x , pr₂ x == x
Σ-up = Σ-ind (λ x → pr₁ x , pr₂ x == x) (λ _ _ → refl)

pair⁼ : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} {w w' : Σ A P} →
        Σ (pr₁ w == pr₁ w') (λ p → transport p (pr₂ w) == pr₂ w') → w == w'
pair⁼ {w = w₁ , w₂} {w₁' , w₂'} (p , q) rewrite p | q = refl

Σ-identity : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} {w w' : Σ A P} →
             (w == w') ≃ Σ (pr₁ w == pr₁ w') λ p → transport p (pr₂ w) == pr₂ w'
Σ-identity {A = A} {P} {w} {w'} = f , qinv→isequiv (pair⁼ {w = w} {w'}, α , β) where
  f : {w w' : Σ A P} → w == w' → Σ (pr₁ w == pr₁ w') λ p → transport p (pr₂ w) == pr₂ w'
  f p rewrite p = refl , refl
  α : {w w' : Σ A P} → f {w} {w'} ∘ (pair⁼ {w = w} {w'}) ~ id
  α {w₁ , w₂} {w₁' , w₂'} (p , q) rewrite p | q = refl
  β : {w w' : Σ A P} → pair⁼ {w = w} {w'} ∘ f ~ id
  β {w₁ , w₂} {w₁' , w₂'} refl = refl
