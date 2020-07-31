{-# OPTIONS --without-K #-}
module HoTT.Universe.Identity where

open import HoTT.Types
open import HoTT.Identity
open import HoTT.Equivalence

module _ {i} {A B : 𝒰 i} where
  idtoeqv : A == B → A ≃ B
  idtoeqv p = transport id p , =-ind
    (λ _ _ p → isequiv (transport _ p))
    (λ _ → qinv→isequiv (id , (λ _ → refl) , (λ _ → refl)))
    A B p

  postulate
    ua : A ≃ B → A == B
    𝒰-identity-β : idtoeqv ∘ ua ~ id
    𝒰-identity-η : ua ∘ idtoeqv ~ id

  -- Axiom 2.10.3
  _ : (A == B) ≃ (A ≃ B)
  _ = idtoeqv , (ua , 𝒰-identity-β) , (ua , 𝒰-identity-η)
