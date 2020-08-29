{-# OPTIONS --without-K #-}
module HoTT.Identity.Coproduct where

open import HoTT.Base
open import HoTT.Equivalence

open variables
private variable x y : A + B

_=+_ : {A : 𝒰 i} {B : 𝒰 j} (x y : A + B) → 𝒰 (i ⊔ j)
_=+_ {j = j} (inl a₁) (inl a₂) = Lift {j} (a₁ == a₂)
_=+_ (inl _) (inr _) = 𝟎
_=+_ (inr _) (inl _) = 𝟎
_=+_ {i} (inr b₁) (inr b₂) = Lift {i} (b₁ == b₂)

=+-equiv : (x == y) ≃ x =+ y
=+-equiv = f , qinv→isequiv (g , η , ε)
  where
  f : x == y → x =+ y
  f {x = inl a} refl = lift refl
  f {x = inr a} refl = lift refl

  g : x =+ y → x == y
  g {x = inl _} {inl _} (lift refl) = refl
  g {x = inl _} {inr _} ()
  g {x = inr _} {inl _} ()
  g {x = inr _} {inr _} (lift refl) = refl

  η : {x y : A + B} → g {x = x} {y} ∘ f ~ id
  η {y = inl _} refl = refl
  η {y = inr _} refl = refl

  ε : f {x = x} {y} ∘ g ~ id
  ε {x = inl _} {inl _} (lift refl) = refl
  ε {x = inl _} {inr _} ()
  ε {x = inr _} {inl _} ()
  ε {x = inr _} {inr _} (lift refl) = refl

=+-elim : x == y → x =+ y
=+-elim = pr₁ =+-equiv

=+-intro : x =+ y → x == y
=+-intro = Iso.g (eqv→iso =+-equiv)
