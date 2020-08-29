{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity.Pi
open import HoTT.Identity.Sigma

module HoTT.Exercises.Chapter2.Exercise11 where

private
  variable
    i j k : Level
    A B C D : 𝒰 i

pullback : (A : 𝒰 i) (B : 𝒰 j) → (A → C) → (B → C) → 𝒰 _
pullback A B ac bc = Σ[ a ∶ A ] Σ[ b ∶ B ] (ac a == bc b)

module Square (ab : A → B) (ac : A → C) (bd : B → D) (cd : C → D)
  where
  IsCommutative = bd ∘ ab ~ cd ∘ ac

  module Commutative (comm : IsCommutative)
    where
    inducedMap : {X : 𝒰 i} → (X → A) → pullback (X → B) (X → C) (bd ∘_) (cd ∘_)
    inducedMap xa = ab ∘ xa , ac ∘ xa , funext (comm ∘ xa)

    IsPullback : ∀ {i} → 𝒰 _
    IsPullback {i} = (X : 𝒰 i) → isequiv (inducedMap {X = X})

  open Commutative public

module _ {ac : A → C} {bc : B → C}
  where
  P = pullback A B ac bc

  open Square.Commutative {A = P} pr₁ (pr₁ ∘ pr₂) ac bc (pr₂ ∘ pr₂)

  prop : IsPullback {i}
  prop X = qinv→isequiv (g , η , ε)
    where
    f = inducedMap
    g : pullback (X → A) (X → B) (ac ∘_) (bc ∘_) → (X → P)
    g (h' , k' , p) x = h' x , k' x , happly p x
    η : g ∘ f ~ id
    η xp = funext λ x → pair⁼ (refl , pair⁼ (refl ,
      happly (=Π-β (pr₂ ∘ pr₂ ∘ xp)) x))
    ε : f ∘ g ~ id
    ε (_ , _ , p) = pair⁼ (refl , pair⁼ (refl , =Π-η p))
