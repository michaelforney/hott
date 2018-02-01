{-# OPTIONS --without-K #-}
module HoTT.Product where

open import HoTT.Types
open import HoTT.Equivalence
open import HoTT.Function
open import HoTT.Homotopy

rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j}
      (C : 𝒰 k) → (A → B → C) → A × B → C
rec _ g (a , b) = g a b

uppt : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j}
       (x : A × B) → pr₁ x , pr₂ x == x
uppt (a , b) = refl

ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k}
      (C : A × B → 𝒰 k) → ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
ind _ g (a , b) = g a b

-- Theorem 2.6.2
identity : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A × B} →
           (x == y) ≃ ((pr₁ x == pr₁ y) × (pr₂ x == pr₂ y))
identity {_} {_} {A} {B} {x} {y} = f , qinv→isequiv (g , α , β)
  where
    f : {x y : A × B} → x == y → (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y)
    f p rewrite p = refl , refl
    g : {x y : A × B} → (pr₁ x == pr₁ y) × (pr₂ x == pr₂ y) → x == y
    g {x = a , b} {a' , b'} (p , q) rewrite p | q = refl
    α : {x y : A × B} → f ∘ g {x} {y} ~ id
    α {a , b} {a' , b'} (p , q) rewrite p | q = refl
    β : {x y : A × B} → g ∘ f {x} {y} ~ id
    β r rewrite r = refl
