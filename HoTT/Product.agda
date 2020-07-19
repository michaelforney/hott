{-# OPTIONS --without-K #-}
module HoTT.Product where

open import HoTT.Types

×-rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j}
        (C : 𝒰 k) → (A → B → C) → A × B → C
×-rec _ g (a , b) = g a b

×-ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j}
        (C : A × B → 𝒰 k) → ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
×-ind _ g (a , b) = g a b

×-uniq : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j}
         (x : A × B) → pr₁ x , pr₂ x == x
×-uniq _ = refl
