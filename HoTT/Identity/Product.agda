{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Identity.Product where

open variables
private variable x y : A × B

_=×_ : A × B → A × B → 𝒰 _
x =× y = pr₁ x == pr₁ y × pr₂ x == pr₂ y

-- Theorem 2.6.2
=× : x == y ≃ x =× y
=× {x = _ , _} {_ , _} = let open Iso in iso→eqv λ where
  .f refl → refl , refl
  .g (refl , refl) → refl
  .η refl → refl
  .ε (refl , refl) → refl

module _ {x y : A × B} where
  open Iso (eqv→iso (=× {x = x} {y})) public
    renaming (f to =×-elim ; g to =×-intro ; η to =×-η ; ε to =×-β)

×-pair⁼ = =×-intro
