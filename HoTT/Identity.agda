module HoTT.Identity where

open import HoTT.Universe
open import HoTT.Empty using (¬)

data _==_ {i} {A : 𝒰 i} (a : A) : A → 𝒰 i where
  refl : a == a

{-# BUILTIN EQUALITY _==_ #-}

infixr 10 _==_

ind : ∀ {i j} {A : 𝒰 i} →
      (C : (x y : A) → x == y → 𝒰 j) → ((x : A) → C x x refl) → (x y : A) → (p : x == y) → C x y p
ind C c x .x refl = c x

ind' : ∀ {i j} {A : 𝒰 i} →
       (a : A) → (C : (x : A) → a == x → 𝒰 j) → C a refl → (x : A) → (p : a == x) → C x p
ind' a C c .a refl = c

_≠_ : ∀ {i} {A : 𝒰 i} → A → A → 𝒰 i
_≠_ x y = ¬ (x == y)
