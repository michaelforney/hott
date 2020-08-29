{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Homotopy

module HoTT.Equivalence where

open variables
private variable C : 𝒰 i

module _ (f : A → B) where
  qinv = Σ[ g ∶ (B → A) ] (g ∘ f ~ id) × (f ∘ g ~ id)

  -- Bi-invertible map
  linv = Σ[ g ∶ (B → A) ] g ∘ f ~ id
  rinv = Σ[ g ∶ (B → A) ] f ∘ g ~ id
  -- The book uses a flipped version rinv × linv for the definition in §2.4.
  biinv = linv × rinv

  -- Half-adjoint equivalence
  ishae = Σ[ g ∶ (B → A) ] Σ[ η ∶ g ∘ f ~ id ] Σ[ ε ∶ f ∘ g ~ id ] ap f ∘ η ~ ε ∘ f

module _ {f : A → B} where
  module qinv (e : qinv f) where
    g = pr₁ e
    η = pr₁ (pr₂ e)
    ε = pr₂ (pr₂ e)

  qinv→linv : qinv f → linv f
  qinv→linv e = g , η
    where open qinv e

  qinv→rinv : qinv f → rinv f
  qinv→rinv e = g , ε
    where open qinv e

  module ishae (e : ishae f) where
    g = pr₁ e
    η = pr₁ (pr₂ e)
    ε = pr₁ (pr₂ (pr₂ e))
    τ = pr₂ (pr₂ (pr₂ e))

  ishae→qinv : ishae f → qinv f
  ishae→qinv e = g , η , ε
    where open ishae e

  qinv→ishae : qinv f → ishae f
  qinv→ishae e = g , η , ε' , τ
    where
    open qinv e
    ε' : f ∘ g ~ id
    ε' b = ε (f (g b)) ⁻¹ ∙ (ap f (η (g b)) ∙ ε b)
    τ : ap f ∘ η ~ ε' ∘ f
    τ a =
      ap f (η a)                        =⟨ unitₗ ⟩
      refl ∙ ap f (η a)                 =⟨ invₗ ⁻¹ ∙ᵣ _ ⟩
      _ ∙ ε (f (g (f a))) ∙ ap f (η a)  =⟨ assoc ⁻¹ ⟩
      _ ∙ (_ ∙ ap f (η a))              =⟨ _ ∙ₗ (_ ∙ₗ ap-id (ap f (η a)) ⁻¹) ⟩
      _ ∙ (ε (f (g (f a))) ∙ ap id _)   =⟨ _ ∙ₗ ~-natural ε (ap f (η a)) ⟩
      _ ∙ (ap (f ∘ g) (ap f (η a)) ∙ _) =⟨ _ ∙ₗ (ap-∘ (f ∘ g) f (η a) ⁻¹ ∙ᵣ _) ⟩
      _ ∙ (ap (f ∘ g ∘ f) (η a) ∙ _)    =⟨ _ ∙ₗ (ap-∘ f (g ∘ f) (η a) ∙ᵣ _) ⟩
      _ ∙ (ap f (ap (g ∘ f) (η a)) ∙ _) =⟨ _ ∙ₗ (ap (ap f) (~-natural-comm η a ⁻¹) ∙ᵣ _) ⟩
      ε' (f a)                          ∎
      where open =-Reasoning

  module biinv (e : biinv f) where
    h = pr₁ (pr₁ e)
    β = pr₂ (pr₁ e)
    g = pr₁ (pr₂ e)
    α = pr₂ (pr₂ e)

  biinv→qinv : biinv f → qinv f
  biinv→qinv e = g , β' , α
    where
    open biinv e
    γ : g ~ h
    γ x = β (g x) ⁻¹ ∙ ap h (α x)
    β' : g ∘ f ~ id
    β' x = γ (f x) ∙ β x

  qinv→biinv : qinv f → biinv f
  qinv→biinv e = (g , η) , (g , ε)
    where open qinv e

module _ {f₁ : B → C} {f₂ : A → B} where
  ishae-∘ : ishae f₁ → ishae f₂ → ishae (f₁ ∘ f₂)
  ishae-∘ e₁ e₂ = g , η , ε , τ
    where
    open ishae e₁ renaming (g to g₁ ; η to η₁ ; ε to ε₁ ; τ to τ₁)
    open ishae e₂ renaming (g to g₂ ; η to η₂ ; ε to ε₂ ; τ to τ₂)
    f = f₁ ∘ f₂
    g = g₂ ∘ g₁
    η : g ∘ f ~ id
    η x = ap g₂ (η₁ (f₂ x)) ∙ η₂ x
    ε : f ∘ g ~ id
    ε x = ap f₁ (ε₂ (g₁ x)) ∙ ε₁ x
    τ : ap f ∘ η ~ ε ∘ f
    τ x =
      ap f (η x)                                       =⟨ ap-∘ f₁ f₂ (ap g₂ (η₁ (f₂ x)) ∙ η₂ x) ⟩
      ap f₁ (ap f₂ (η x))                              =⟨ ap (ap f₁) (ap-∙ f₂ (ap g₂ (η₁ (f₂ x))) (η₂ x)) ⟩
      ap f₁ (ap f₂ (ap g₂ (η₁ (f₂ x))) ∙ ap f₂ (η₂ x)) =⟨ ap (ap f₁) (ap f₂ _ ∙ₗ τ₂ x) ⟩
      ap f₁ (ap f₂ (ap g₂ (η₁ (f₂ x))) ∙ ε₂ (f₂ x))    =⟨ ap (ap f₁) (ap-∘ f₂ g₂ _ ⁻¹ ∙ᵣ ε₂ (f₂ x)) ⟩
      ap f₁ (ap (f₂ ∘ g₂) (η₁ (f₂ x)) ∙ ε₂ (f₂ x))     =⟨ ap (ap f₁) (~-natural ε₂ (η₁ (f₂ x))) ⁻¹ ⟩
      ap f₁ (ε₂ (g₁ (f x)) ∙ ap id (η₁ (f₂ x)))        =⟨ ap (ap f₁) (ε₂ (g₁ (f x)) ∙ₗ ap-id (η₁ (f₂ x))) ⟩
      ap f₁ (ε₂ (g₁ (f x)) ∙ η₁ (f₂ x))                =⟨ ap-∙ f₁ (ε₂ (g₁ (f x))) (η₁ (f₂ x)) ⟩
      ap f₁ (ε₂ (g₁ (f x))) ∙ ap f₁ (η₁ (f₂ x))        =⟨ _ ∙ₗ τ₁ (f₂ x) ⟩
      ε (f x)                                          ∎
      where open =-Reasoning

  biinv-∘ : biinv f₁ → biinv f₂ → biinv (f₁ ∘ f₂)
  biinv-∘ e₁ e₂ = (h , β) , (g , α)
    where
    open biinv e₁ renaming (h to h₁ ; β to β₁ ; g to g₁ ; α to α₁)
    open biinv e₂ renaming (h to h₂ ; β to β₂ ; g to g₂ ; α to α₂)
    f = f₁ ∘ f₂
    h = h₂ ∘ h₁
    β : h ∘ f ~ id
    β x = ap h₂ (β₁ (f₂ x)) ∙ β₂ x
    g = g₂ ∘ g₁
    α : f ∘ g ~ id
    α x = ap f₁ (α₂ (g₁ x)) ∙ α₁ x

-- Choose isequiv :≡ biinv since it is quicker to compute.
isequiv = biinv
qinv→isequiv = qinv→biinv
isequiv→qinv = biinv→qinv
isequiv-∘ = biinv-∘

_≃_ : 𝒰 i → 𝒰 j → 𝒰 (i ⊔ j)
A ≃ B = Σ (A → B) isequiv
infixr 5 _≃_

record Iso (A : 𝒰 i) (B : 𝒰 j) : 𝒰 (i ⊔ j) where
  field
    f : A → B
    g : B → A
    η : g ∘ f ~ id
    ε : f ∘ g ~ id

iso→eqv : Iso A B → A ≃ B
iso→eqv iso = f , qinv→isequiv (g , η , ε)
  where open Iso iso

eqv→iso : A ≃ B → Iso A B
eqv→iso e = record { f = pr₁ e ; g = g ; η = η ; ε = ε }
  where open qinv (isequiv→qinv (pr₂ e))

module Eqv {i} {j} {A : 𝒰 i} {B : 𝒰 j} (e : A ≃ B) = Iso (eqv→iso e)

-- Lemma 2.4.12
--  (i)
reflₑ : A ≃ A
reflₑ = id , qinv→isequiv (id , (λ _ → refl) , (λ _ → refl))

--  (ii)
_⁻¹ₑ : A ≃ B → B ≃ A
e ⁻¹ₑ = g , qinv→isequiv (pr₁ e , ε , η)
  where
  open qinv (isequiv→qinv (pr₂ e))
infix 30 _⁻¹ₑ

--  (iii)
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
e₁ ∙ₑ e₂ = pr₁ e₂ ∘ pr₁ e₁ , isequiv-∘ (pr₂ e₂) (pr₂ e₁)
infixl 20 _∙ₑ_

idtoeqv : A == B → A ≃ B
idtoeqv p = transport id p , e
  where
  e : isequiv (transport id p)
  e rewrite p = pr₂ reflₑ

module ≃-Reasoning
  where
  _≃⟨_⟩_ : (A : 𝒰 i) → A ≃ B → B ≃ C → A ≃ C
  x ≃⟨ e₁ ⟩ e₂ = e₁ ∙ₑ e₂
  infixr 2 _≃⟨_⟩_

  _∎ : (A : 𝒰 i) → A ≃ A
  _ ∎ = reflₑ
  infix 3 _∎
