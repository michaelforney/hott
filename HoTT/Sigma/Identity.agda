{-# OPTIONS --without-K #-}
module HoTT.Sigma.Identity where

open import HoTT.Types
open import HoTT.Identity
open import HoTT.Equivalence

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
