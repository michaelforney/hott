module HoTT.Empty where

open import HoTT.Types

¬ : ∀ {i} (A : 𝒰 i) → 𝒰 i
¬ A = A → 𝟎

rec : ∀ {i} (C : 𝒰 i) → 𝟎 → C
rec C ()

ind : ∀ {i} (C : 𝟎 → 𝒰 i) → (z : 𝟎) → C z
ind C ()
