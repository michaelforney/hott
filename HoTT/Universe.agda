module HoTT.Universe where

open import Agda.Primitive

𝒰 : (i : Level) → Set (lsuc i)
𝒰 i = Set i

𝒰₀ : Set₁
𝒰₀ = Set
