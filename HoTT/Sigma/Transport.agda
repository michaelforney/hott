{-# OPTIONS --without-K #-}
module HoTT.Sigma.Transport where

open import HoTT.Base
open import HoTT.Identity
open import HoTT.Identity.Sigma

Σ-transport : ∀ {i j k} {A : 𝒰 i} {P : A → 𝒰 j} {Q : (Σ A λ x → P x) → 𝒰 k} {x y : A} →
              (p : x == y) (uz : Σ (P x) λ u → Q (x , u)) →
              transport (λ x → Σ (P x) λ u → Q (x , u)) p uz ==
                transport _ p (pr₁ uz) , transport Q (pair⁼ (p , refl)) (pr₂ uz)
Σ-transport refl (u , z) = refl
