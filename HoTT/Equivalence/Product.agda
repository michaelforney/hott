{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity.Product

module HoTT.Equivalence.Product where

private
  variable
    i : Level
    A A' B B' : 𝒰 i

×-swap : A × B → B × A
×-swap x = pr₂ x , pr₁ x

×-comm : A × B ≃ B × A
×-comm = ×-swap , qinv→isequiv (×-swap , ×-uniq , ×-uniq)

×-equiv₁ : A ≃ A' → A × B ≃ A' × B
×-equiv₁ {A = A} {A' = A'} {B = B} (f₁ , e₁) = f , qinv→isequiv (g , η , ε)
  where
  open qinv (isequiv→qinv e₁) renaming (g to g₁ ; η to η₁ ; ε to ε₁)
  f : A × B → A' × B
  f (a , b) = f₁ a , b
  g : A' × B → A × B
  g (a' , b) = g₁ a' , b
  η : g ∘ f ~ id
  η (a , b) = ×-pair⁼ (η₁ a , refl)
  ε : f ∘ g ~ id
  ε (a' , b) = ×-pair⁼ (ε₁ a' , refl)

×-equiv₂ : B ≃ B' → A × B ≃ A × B'
×-equiv₂ {B = B} {B' = B'} {A = A} (f₂ , e₂) = f , qinv→isequiv (g , η , ε)
  where
  open qinv (isequiv→qinv e₂) renaming (g to g₂ ; η to η₂ ; ε to ε₂)
  f : A × B → A × B'
  f (a , b) = a , f₂ b
  g : A × B' → A × B
  g (a , b') = a , g₂ b'
  η : g ∘ f ~ id
  η (a , b) = ×-pair⁼ (refl , η₂ b)
  ε : f ∘ g ~ id
  ε (a , b') = ×-pair⁼ (refl , ε₂ b')
