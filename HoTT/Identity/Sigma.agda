{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Equivalence

module HoTT.Identity.Sigma where

open variables

_=Σ_ : Σ A P → Σ A P → 𝒰 _
_=Σ_ {P = P} x y = Σ[ p ∶ x₁ == y₁ ] transport P p x₂ == y₂
  where
  open Σ x renaming (pr₁ to x₁ ; pr₂ to x₂)
  open Σ y renaming (pr₁ to y₁ ; pr₂ to y₂)

pair⁼' : {x y : Σ A P} → Σ[ p ∶ pr₁ x == pr₁ y ] pr₂ x == transport P (p ⁻¹) (pr₂ y) → x == y
pair⁼' {x = _ , _} {y = _ , _} (refl , refl) = refl

=Σ-equiv : {x y : Σ A P} → (x == y) ≃ x =Σ y
=Σ-equiv {x = _ , _} {y = _ , _} = let open Iso in iso→eqv λ where
  .f refl → (refl , refl)
  .g (refl , refl) → refl
  .η refl → refl
  .ε (refl , refl) → refl

pair⁼ : {x y : Σ A P} → x =Σ y → x == y
pair⁼ = Iso.g (eqv→iso =Σ-equiv)
