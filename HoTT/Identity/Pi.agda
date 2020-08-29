{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity

module HoTT.Identity.Pi where

open variables
private variable f g h : Π A P

module _ {f g : Π A P} where
  -- Axiom 2.9.3 - function extensionality
  postulate
    happly-isequiv : isequiv (happly {f = f} {g})

  module _ where
    open qinv (isequiv→qinv happly-isequiv) renaming (g to happly⁻¹)
    abstract
      funext : f ~ g → f == g
      funext = happly⁻¹
      =Π-η : funext ∘ happly ~ id
      =Π-η = η
      =Π-β : happly ∘ funext ~ id
      =Π-β = ε

=Π-equiv : f == g ≃ f ~ g
=Π-equiv = happly , happly-isequiv

funext-∙ₕ : (α : f ~ g) (β : g ~ h) → funext (α ∙ₕ β) == funext α ∙ funext β
funext-∙ₕ α β = ap funext (funext λ x → (happly (=Π-β α) x ⋆ happly (=Π-β β) x) ⁻¹) ∙ p
  where
  p : funext (happly (funext α) ∙ₕ happly (funext β)) == funext α ∙ funext β
  p rewrite funext α rewrite funext β = =Π-η refl

funext-ap : {P : A → 𝒰 i} {Q : A → 𝒰 j} {g h : Π A P}
            (f : {a : A} → P a → Q a) (α : g ~ h) →
            funext (ap f ∘ α) == ap (f ∘_) (funext α)
funext-ap f α = ap (λ α → funext (ap f ∘ α)) (=Π-β α) ⁻¹ ∙ p
  where
  p : funext (ap f ∘ happly (funext α)) == ap (f ∘_) (funext α)
  p rewrite funext α = =Π-η refl
