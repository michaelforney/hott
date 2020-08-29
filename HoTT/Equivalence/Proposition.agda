{-# OPTIONS --without-K #-}
module HoTT.Equivalence.Proposition where

open import HoTT.Base
open import HoTT.HLevel
open import HoTT.Equivalence

open variables

-- Proven by Theorem 4.3.2
postulate
  isequiv-prop : {f : A → B} → isProp (isequiv f)

{-
  fib : B → 𝒰 _
  fib y = Σ[ x ∶ A ] (f x == y)

  -- Left inverse with coherence
  lcoh : linv → 𝒰 _
  lcoh (g , η) = Σ[ ε ∶ f ∘ g ~ id ] ap g ∘ ε ~ η ∘ g

  -- Right inverse with coherence
  rcoh : rinv → 𝒰 _
  rcoh (g , ε) = Σ[ η ∶ g ∘ f ~ id ] ap f ∘ η ~ ε ∘ f
-}

{-
hae-fib-contr : {f : A → B} → ishae f → (y : B) → isContr (fib f y)
hae-fib-contr {A = A} {f = f} (g , η , ε , τ) y = (g y , ε y) , contr
  where
  contr : (z : fib f y) → (g y , ε y) == z
  contr (x , p) = pair⁼ (qₓ , qₚ)
    where
    qₓ : g y == x
    qₓ = ap g p ⁻¹ ∙ η x
    qₚ : transport (λ x → f x == y) qₓ (ε y) == p
    qₚ = begin
      transport (λ x → f x == y) qₓ (ε y)      =⟨ transport=-constᵣ f y qₓ (ε y) ⟩
      ap f qₓ ⁻¹ ∙ ε y                         =⟨ ap (λ p → p ⁻¹ ∙ ε y) (ap-∙ f (ap g p ⁻¹) (η x)) ⟩
      (ap f (ap g p ⁻¹) ∙ ap f (η x)) ⁻¹ ∙ ε y =⟨ ap (λ p → p ⁻¹ ∙ ε y) (ap (ap f) (ap-⁻¹ g p ⁻¹) ⋆ τ x) ⟩
      (ap f (ap g (p ⁻¹)) ∙ ε (f x)) ⁻¹ ∙ ε y  =⟨ ap (λ p → (p ∙ ε (f x)) ⁻¹ ∙ ε y) (ap-∘ f g (p ⁻¹)) ⟩
      (ap (f ∘ g) (p ⁻¹) ∙ ε (f x)) ⁻¹ ∙ ε y   =⟨ ap (λ p → p ⁻¹ ∙ ε y) (~-naturality ε (p ⁻¹) ⁻¹) ⟩
      (ε y ∙ ap id (p ⁻¹)) ⁻¹ ∙ ε y            =⟨ ap (λ p → (ε y ∙ p) ⁻¹ ∙ ε y) (ap-id (p ⁻¹)) ⟩
      (ε y ∙ p ⁻¹) ⁻¹ ∙ ε y                    =⟨ ∙-⁻¹ (ε y) (p ⁻¹) ∙ᵣ ε y ⟩
      p ⁻¹ ⁻¹ ∙ ε y ⁻¹ ∙ ε y                   =⟨ ∙-assoc _ _ _ ⁻¹ ⟩
      p ⁻¹ ⁻¹ ∙ (ε y ⁻¹ ∙ ε y)                 =⟨ invinv p ⋆ ∙-invₗ (ε y) ⟩
      p ∙ refl                                 =⟨ ∙-unitᵣ p ⁻¹ ⟩
      p                                        ∎
      where
      open =-Reasoning
      ∙-⁻¹ : {A : 𝒰 i} {x y z : A} (p : x == y) (q : y == z) → (p ∙ q) ⁻¹ == q ⁻¹ ∙ p ⁻¹
      ∙-⁻¹ refl refl = refl
      invinv : {A : 𝒰 i} {x y : A} (p : x == y) → p ⁻¹ ⁻¹ == p
      invinv refl = refl

linv-contr : {f : A → B} → qinv f → isContr (linv f)
linv-contr {f = f} (g , η , ε) = {!hae-fib-contr (qinv→ishae e)!}
  where
  q' : qinv (_∘ f)
  q' = _∘ g , (λ x → ap (x ∘_) {!funext ?!}) , {!!}
rinv-contr : {f : A → B} → qinv f → isContr (rinv f)
rinv-contr = {!!}
-}
