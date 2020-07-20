{-# OPTIONS --without-K #-}
module HoTT.Product.Identity where

open import HoTT.Types
open import HoTT.Equivalence

pair⁼ : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A × B} →
        (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y) → x == y
pair⁼ {x = _ , _} {_ , _} (refl , refl) = refl

-- Theorem 2.6.2
×-identity : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A × B} →
             (x == y) ≃ ((pr₁ x == pr₁ y) × (pr₂ x == pr₂ y))
×-identity {_} {_} {A} {B} {x} {y} = f , qinv→isequiv (pair⁼ , α , β)
  where
    f : {x y : A × B} → x == y → (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y)
    f refl = refl , refl
    α : {x y : A × B} → f ∘ pair⁼ {x = x} {y} ~ id
    α {_ , _} {_ , _} (refl , refl) = refl
    β : {x y : A × B} → pair⁼ ∘ f {x} {y} ~ id
    β refl = refl
