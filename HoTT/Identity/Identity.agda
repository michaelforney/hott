{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Equivalence
open import HoTT.Homotopy

module HoTT.Identity.Identity where

ap⁻¹ : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} ((f , _) : A ≃ B) {a a' : A} →
       f a == f a' → a == a'
ap⁻¹ e {a} {a'} p = η a ⁻¹ ∙ ap g p ∙ η a'
  where open Iso (eqv→iso e)

-- Theorem 2.11.1
ap≃ : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} →
      ((f , _) : A ≃ B) → (a a' : A) → (a == a') ≃ (f a == f a')
ap≃ e a a' = iso→eqv iso
  where
  open Iso (eqv→iso e)
  iso : Iso _ _
  Iso.f iso = ap f
  Iso.g iso = ap⁻¹ e
  Iso.η iso p =
    η a ⁻¹ ∙ ap g (ap f p) ∙ η a'   =⟨ _ ∙ₗ ap-∘ g f p ⁻¹ ∙ᵣ _ ⟩
    η a ⁻¹ ∙ ap (g ∘ f) p ∙ η a'    =⟨ assoc ⁻¹ ⟩
    η a ⁻¹ ∙ (ap (g ∘ f) p ∙ η a')  =⟨ pivotₗ (~-natural-id η p) ⁻¹ ⟩
    p                               ∎
    where open =-Reasoning
  Iso.ε iso q =
    ap f (η a ⁻¹ ∙ ap g q ∙ η a')                 =⟨ pivotₗ (~-natural (ε ∘ f) _) ⟩
    ε (f a) ⁻¹ ∙ (ap (f ∘ g ∘ f) _ ∙ ε (f a'))    =⟨ _ ∙ₗ (ap-∘ f (g ∘ f) _ ∙ᵣ _) ⟩
    ε (f a) ⁻¹ ∙ (ap f (ap (g ∘ f) _) ∙ ε (f a')) =⟨ ap (λ p → _ ∙ (ap f p ∙ _)) inner ⟩
    ε (f a) ⁻¹ ∙ (ap f (ap g q) ∙ ε (f a'))       =⟨ _ ∙ₗ (ap-∘ f g q ⁻¹ ∙ᵣ _) ⟩
    ε (f a) ⁻¹ ∙ (ap (f ∘ g) q ∙ ε (f a'))        =⟨ pivotₗ (~-natural-id ε q) ⁻¹ ⟩
    q                                             ∎
    where
    open =-Reasoning
    inner : ap (g ∘ f) (η a ⁻¹ ∙ ap g q ∙ η a') == ap g q
    inner =
      ap (g ∘ f) (η a ⁻¹ ∙ ap g q ∙ η a')      =⟨ pivotᵣ (~-natural-id η _ ⁻¹) ⟩
      η a ∙ (η a ⁻¹ ∙ ap g q ∙ η a') ∙ η a' ⁻¹ =⟨ assoc ∙ᵣ η a' ⁻¹ ⟩
      η a ∙ (η a ⁻¹ ∙ ap g q) ∙ η a' ∙ η a' ⁻¹ =⟨ assoc ∙ᵣ _ ∙ᵣ _ ⟩
      η a ∙ η a ⁻¹ ∙ ap g q ∙ η a' ∙ η a' ⁻¹   =⟨ invᵣ ∙ᵣ _ ∙ᵣ _ ∙ᵣ _ ⟩
      refl ∙ ap g q ∙ η a' ∙ η a' ⁻¹           =⟨ unitₗ ⁻¹ ∙ᵣ _ ∙ᵣ _ ⟩
      ap g q ∙ η a' ∙ η a' ⁻¹                  =⟨ assoc ⁻¹ ⟩
      ap g q ∙ (η a' ∙ η a' ⁻¹)                =⟨ _ ∙ₗ invᵣ ⟩
      ap g q ∙ refl                            =⟨ unitᵣ ⁻¹ ⟩
      ap g q                                   ∎

-- Theorem 2.11.3
=-transport : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {a a' : A}
                (f g : A → B) (p : a == a') (q : f a == g a) →
                transport (λ x → f x == g x) p q == ap f p ⁻¹ ∙ q ∙ ap g p
=-transport _ _ refl q rewrite q = refl

module _ {i} {A : 𝒰 i} {x₁ x₂ : A} (a : A) (p : x₁ == x₂)
  where
  =-transportₗ : (q : a == x₁) → transport (a ==_) p q == q ∙ p
  =-transportₗ q rewrite p = unitᵣ

  =-transportᵣ : (q : x₁ == a) → transport (_== a) p q == p ⁻¹ ∙ q
  =-transportᵣ q rewrite p = unitₗ
