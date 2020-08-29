{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Identity.Boolean where

private
  variable
    x y : 𝟐

_=𝟐_ : 𝟐 → 𝟐 → 𝒰₀
0₂ =𝟐 0₂ = 𝟏
0₂ =𝟐 1₂ = 𝟎
1₂ =𝟐 0₂ = 𝟎
1₂ =𝟐 1₂ = 𝟏

=𝟐-equiv : x == y ≃ x =𝟐 y
=𝟐-equiv = f , qinv→isequiv (g , η , ε)
  where
  f : x == y → x =𝟐 y
  f {0₂} p = transport (0₂ =𝟐_) p ★
  f {1₂} p = transport (1₂ =𝟐_) p ★
  g : x =𝟐 y → x == y
  g {0₂} {0₂} _ = refl
  g {0₂} {1₂} ()
  g {1₂} {0₂} ()
  g {1₂} {1₂} _ = refl
  η : g ∘ f {x} {y} ~ id
  η {0₂} refl = refl
  η {1₂} refl = refl
  ε : f ∘ g {x} {y} ~ id
  ε {0₂} {0₂} ★ = refl
  ε {0₂} {1₂} ()
  ε {1₂} {0₂} ()
  ε {1₂} {1₂} ★ = refl
