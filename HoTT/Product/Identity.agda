{-# OPTIONS --without-K #-}
module HoTT.Product.Identity where

open import HoTT.Types
open import HoTT.Equivalence

-- Theorem 2.6.2
×-identity : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A × B} →
             (x == y) ≃ ((pr₁ x == pr₁ y) × (pr₂ x == pr₂ y))
×-identity {_} {_} {A} {B} {x} {y} = f , qinv→isequiv (g , α , β)
  where
    f : {x y : A × B} → x == y → (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y)
    f p rewrite p = refl , refl
    g : {x y : A × B} → (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y) → x == y
    g {x = a , b} {a' , b'} (p , q) rewrite p | q = refl
    α : {x y : A × B} → f ∘ g {x} {y} ~ id
    α {a , b} {a' , b'} (p , q) rewrite p | q = refl
    β : {x y : A × B} → g ∘ f {x} {y} ~ id
    β r rewrite r = refl
