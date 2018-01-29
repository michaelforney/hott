module HoTT.Product where

open import Agda.Primitive
open import HoTT.Universe
open import HoTT.Identity hiding (ind)

record _×_ {i j} (A : 𝒰 i) (B : 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B

rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} (C : 𝒰 k) →
      (A → B → C) → A × B → C
rec C g (a , b) = g a b

uppt : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} →
       (x : A × B) → _×_.pr₁ x , _×_.pr₂ x == x
uppt (a , b) = refl

ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} →
      (C : A × B → 𝒰 k) → ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
ind C g (a , b) = g a b
