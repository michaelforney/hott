{-# OPTIONS --without-K #-}
module HoTT.Empty where

open import HoTT.Types

¬_ : ∀ {i} (A : 𝒰 i) → 𝒰 i
¬_ A = A → 𝟎
infix 25 ¬_

rec : ∀ {i} (C : 𝒰 i) → 𝟎 → C
rec C ()

ind : ∀ {i} (C : 𝟎 → 𝒰 i) → (z : 𝟎) → C z
ind C ()
