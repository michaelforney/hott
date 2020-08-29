{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Equivalence.Empty where

open variables

𝟎-equiv : {A : 𝒰 i} → ¬ A → 𝟎 {i} ≃ A
𝟎-equiv ¬a = 𝟎-rec , qinv→isequiv (𝟎-rec ∘ ¬a , 𝟎-ind , 𝟎-rec ∘ ¬a)
