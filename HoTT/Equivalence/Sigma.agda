{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Equivalence
open import HoTT.Identity.Sigma

module HoTT.Equivalence.Sigma where

open variables

Σ-equiv₁ : ((f , _) : A ≃ B) → Σ A (P ∘ f) ≃ Σ B P
Σ-equiv₁ {A = A} {B} {P = P} (f , e) = iso→eqv iso
  where
  open ishae (qinv→ishae (isequiv→qinv e))
  iso : Iso _ _
  Iso.f iso (a , b) = f a , b
  Iso.g iso (a' , b) = g a' , transport P (ε a' ⁻¹) b
  Iso.η iso (a , b) = pair⁼ (η a , (
    transport (P ∘ f) (η a) (transport P (ε (f a) ⁻¹) b)  =⟨ transport-ap P f (η a) _ ⁻¹ ⟩
    transport P (ap f (η a)) (transport P (ε (f a) ⁻¹) b) =⟨ transport-∙ P (ε (f a) ⁻¹) (ap f (η a)) b ⁻¹ ⟩
    transport P (ε (f a) ⁻¹ ∙ ap f (η a)) b               =⟨ ap (λ p → transport P p b) (ε (f a) ⁻¹ ∙ₗ τ a) ⟩
    transport P (ε (f a) ⁻¹ ∙ ε (f a)) b                  =⟨ ap (λ p → transport P p b) (invₗ {p = ε (f a)}) ⟩
    b ∎))
    where open =-Reasoning
  Iso.ε iso (a' , b) rewrite ε a' = refl

Σ-equiv₂ : ((x : A) → P x ≃ Q x) → Σ A P ≃ Σ A Q
Σ-equiv₂ {A = A} {P = P} {Q = Q} e = iso→eqv iso
  where
  iso : Iso (Σ A P) (Σ A Q)
  Iso.f iso x = let (a , b) = x in a , pr₁ (e a) b
  Iso.g iso (a , b') = a , g b'
    where open qinv (isequiv→qinv (pr₂ (e a)))
  Iso.η iso (a , b) = pair⁼ (refl , η b)
    where open qinv (isequiv→qinv (pr₂ (e a)))
  Iso.ε iso (a , b') = pair⁼ (refl , ε b')
    where open qinv (isequiv→qinv (pr₂ (e a)))

Σ-equiv : ((f , _) : A ≃ B) → ((x : A) → P x ≃ Q (f x)) → Σ A P ≃ Σ B Q
Σ-equiv e₁ e₂ = Σ-equiv₂ e₂ ∙ₑ Σ-equiv₁ e₁

Σ-assoc : {C : Σ A P → 𝒰 i} →
          Σ[ x ∶ A ] Σ[ y ∶ P x ] C (x , y) ≃ Σ[ p ∶ Σ A P ] C p
Σ-assoc = let open Iso in iso→eqv λ where
  .f ( x , y  , z) → (x , y) , z
  .g ((x , y) , z) →  x , y  , z
  .η ( _ , _  , _) → refl
  .ε ((_ , _) , _) → refl

Σ-comm : {P : A → B → 𝒰 i} →
         Σ[ x ∶ A ] Σ[ y ∶ B ] (P x y) ≃ Σ[ y ∶ B ] Σ[ x ∶ A ] (P x y)
Σ-comm = let open Iso in iso→eqv λ where
  .f (a , b , p) → (b , a , p)
  .g (b , a , p) → (a , b , p)
  .η (a , b , p) → refl
  .ε (b , a , p) → refl
