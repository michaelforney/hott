module HoTT.Pi where

open import HoTT.Types
open import HoTT.Equivalence
open import HoTT.Homotopy

module _ {i j} {A : 𝒰 i} {B : A → 𝒰 j} {f g : Π A B} where
  happly : f == g → f ~ g
  happly refl x = refl

  postulate
    funext : f ~ g → f == g
    Π-identity-β : happly ∘ funext ~ id
    Π-identity-η : funext ∘ happly ~ id

  -- Axiom 2.9.3
  _ : (f == g) ≃ (f ~ g)
  _ = happly , (funext , Π-identity-β) , (funext , Π-identity-η)
