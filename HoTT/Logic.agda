{-# OPTIONS --without-K --rewriting #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Identity.Sigma
open import HoTT.Identity.Pi
open import HoTT.Identity.Universe
open import HoTT.Identity.Product
open import HoTT.HLevel
open import HoTT.HLevel.Truncate
open import HoTT.Equivalence
open import HoTT.Equivalence.Lift

module HoTT.Logic where

private variable i j k : Level

LiftProp : Prop𝒰 i → Prop𝒰 (i ⊔ j)
LiftProp {i} {j} P = type (Lift {j} (P ty))

⊤ : Prop𝒰 i
⊤ = type 𝟏

⊥ : Prop𝒰 i
⊥ = type 𝟎

_∧_ : Prop𝒰 i → Prop𝒰 j → Prop𝒰 (i ⊔ j)
P ∧ Q = type (P ty × Q ty) ⦃ ×-hlevel ⦄

_⇒_ : Prop𝒰 i → Prop𝒰 j → Prop𝒰 (i ⊔ j)
P ⇒ Q = type (P ty → Q ty)
infix 10 _⇒_

_⇔_ : Prop𝒰 i → Prop𝒰 i → Prop𝒰 (lsuc i)
P ⇔ Q = type (P ty == Q ty) ⦃ equiv-hlevel (=𝒰-equiv ⁻¹ₑ) ⦄
  where
  instance
    _ = Σ-hlevel
    _ = raise ⦃ hlevel𝒰.h P ⦄
    _ = raise ⦃ hlevel𝒰.h Q ⦄

_∨_ : Prop𝒰 i → Prop𝒰 j → Prop𝒰 (i ⊔ j)
P ∨ Q = type ∥ P ty + Q ty ∥

∃ : (A : 𝒰 i) → (A → Prop𝒰 j) → Prop𝒰 (i ⊔ j)
∃ A P = type ∥ Σ A (_ty ∘ P) ∥
syntax ∃ A (λ x → Φ) = ∃[ x ∶ A ] Φ

∀' : (A : 𝒰 i) → (P : A → Prop𝒰 j) → Prop𝒰 (i ⊔ j)
∀' A P = type (Π A (_ty ∘ P))
  where instance _ = λ {x} → hlevel𝒰.h (P x)
syntax ∀' A (λ x → Φ) = ∀[ x ∶ A ] Φ

LEM : 𝒰 (lsuc i)
LEM {i} = (A : Prop𝒰 i) → A ty + ¬ A ty

LEM∞ : 𝒰 (lsuc i)
LEM∞ {i} = (A : 𝒰 i) → A + ¬ A

LDN : 𝒰 (lsuc i)
LDN {i} = (A : Prop𝒰 i) → ¬ ¬ A ty → A ty

AC : 𝒰 (lsuc i ⊔ lsuc j ⊔ lsuc k)
AC {i} {j} {k} =
  {X : 𝒰 i} {A : X → 𝒰 j} {P : (x : X) → A x → 𝒰 k} →
  ⦃ hlevel 2 X ⦄ → ⦃ {x : X} → hlevel 2 (A x) ⦄ →
  ⦃ {x : X} {a : A x} → hlevel 1 (P x a) ⦄ →
  Π[ x ∶ X ] ∥ Σ[ a ∶ A x ] P x a ∥ →
  ∥ Σ[ g ∶ Π[ x ∶ X ] A x ] Π[ x ∶ X ] P x (g x) ∥

Lemma3/9/1 : (P : 𝒰 i) → ⦃ hlevel 1 P ⦄ → P ≃ ∥ P ∥
Lemma3/9/1 P = let open Iso in iso→eqv λ where
  .f → ∣_∣ ; .g → ∥-rec id ; .η _ → refl ; .ε _ → center

-- Principle of unique choice
Corollary3/9/2 : {A : 𝒰 i} {P : A → 𝒰 i} → ⦃ {x : A} → hlevel 1 (P x) ⦄ →
                 ((x : A) → ∥ P x ∥) → (x : A) → P x
Corollary3/9/2 {P = P} f = ∥-rec id ∘ f
