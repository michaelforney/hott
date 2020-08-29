{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence

module HoTT.Identity.Universe {i} {A B : 𝒰 i} where

-- Axiom 2.10.3 - univalence
postulate
  idtoeqv-equiv : isequiv (idtoeqv {A = A} {B = B})

=𝒰-equiv : (A == B) ≃ (A ≃ B)
=𝒰-equiv = idtoeqv , idtoeqv-equiv

module _ where
  open qinv (isequiv→qinv idtoeqv-equiv)
  abstract
    ua : A ≃ B → A == B
    ua = g
    =𝒰-η : ua ∘ idtoeqv ~ id
    =𝒰-η = η
    =𝒰-β : idtoeqv ∘ ua ~ id
    =𝒰-β = ε

_=𝒰_ = _≃_
