{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity

module HoTT.Homotopy where

open variables
private variable f g : A → B

-- Lemma 2.4.3
~-natural : (α : f ~ g) {x y : A} (p : x == y) → α x ∙ ap g p == ap f p ∙ α y
~-natural α {x} refl rewrite α x = refl

~-natural-id : (α : f ~ id) {x y : A} (p : x == y) → α x ∙ p == ap f p ∙ α y
~-natural-id α {x} refl rewrite α x = refl

-- Corollary 2.4.4
~-natural-comm : {f : A → A} (α : f ~ id) → α ∘ f ~ ap f ∘ α
~-natural-comm {f = f} α x = cancelᵣ (α (f x) ∙ₗ ap-id (α x) ⁻¹ ∙ ~-natural α (α x))

module ~-Reasoning where
  _~⟨_⟩_ : (f : Π A P) {g h : Π A P} → f ~ g → g ~ h → f ~ h
  x ~⟨ α ⟩ β = α ∙ₕ β
  infixr 2 _~⟨_⟩_

  _∎ : (f : Π A P) → f ~ f
  _ ∎ = reflₕ
  infix 3 _∎
