module HoTT.Function where

open import HoTT.Universe

id : ∀ {i} {A : 𝒰 i} → A → A
id x = x

_∘_ : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} →
      (B → C) → (A → B) → (A → C)
_∘_ f g x = f (g x)
infixr 30 _∘_
