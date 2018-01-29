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

-- Lemma 2.1.1
_⁻¹ : ∀ {i} {A : 𝒰 i} {x y : A} → x == y → y == x
_⁻¹ {i} {A} {x} {y} p = ind D d x y p
  where
    D : (x y : A) → x == y → 𝒰 i
    D x y p = y == x
    d : (x : A) → D x x refl
    d x = refl
infix 30 _⁻¹

-- Lemma 2.1.2
_∙_ : ∀ {i} {A : 𝒰 i} {x y z : A} → x == y → y == z → x == z
_∙_ {i} {A} {x} {y} {z} p q = ind D d x y p z q where
  E : (x z : A) (q : x == z) → 𝒰 i
  E x z q = x == z
  e : (x : A) → E x x refl
  e x = refl
  D : (x y : A) → x == y → 𝒰 i
  D x y p = (z : A) (q : y == z) → x == z
  d : (x : A) → D x x refl
  d x z q = ind E e x z q
infixl 20 _∙_
