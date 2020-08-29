{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Equivalence
open import HoTT.Equivalence.Sigma
open import HoTT.Identity.Sigma
open import HoTT.Identity.Pi
open import HoTT.Transport.Identity
open import HoTT.HLevel
open import HoTT.Exercises.Chapter2.Exercise11 using (module Square ; pullback)

module HoTT.Exercises.Chapter2.Exercise12
  {i} {A B C D E F : 𝒰 i}
  {ac : A → C} {ab : A → B} {cd : C → D} {bd : B → D}
  {ce : C → E} {ef : E → F}              {df : D → F} where

module Squareₗ = Square ac ab cd bd
module Squareᵣ = Square ce cd ef df
module Squareₒ = Square (ce ∘ ac) ab ef (df ∘ bd)

module _ {commₗ : Squareₗ.IsCommutative} {commᵣ : Squareᵣ.IsCommutative}
         {pullbackᵣ : Squareᵣ.IsPullback commᵣ {i}}
  where
  commₒ : Squareₒ.IsCommutative
  commₒ = commᵣ ∘ ac ∙ₕ ap df ∘ commₗ

  open Squareₗ.Commutative commₗ using () renaming (inducedMap to fₗ)
  open Squareᵣ.Commutative commᵣ using () renaming (inducedMap to fᵣ)
  open Squareₒ.Commutative commₒ using () renaming (inducedMap to fₒ)

  -- Solution based on https://pcapriotti.github.io/hott-exercises/chapter2.ex12.core.html
  equiv : (X : 𝒰 i) →
          pullback (X → C) (X → B) (cd ∘_) (bd ∘_) ≃
          pullback (X → E) (X → B) (ef ∘_) ((df ∘ bd) ∘_)
  equiv X =
    -- Use pullbackᵣ to expand X → C to pullback (X → E) (X → D) (ef ∘_) (df ∘_)
    pullback (X → C) (X → B) (cd ∘_) (bd ∘_)
      ≃⟨ Σ-equiv₁ (fᵣ , pullbackᵣ X) ⟩
    -- Reassociate pairs
    Σ[ (_ , xd , _) ∶ pullback (X → E) (X → D) (ef ∘_) (df ∘_) ] Σ[ xb ∶ (X → B) ] (xd == bd ∘ xb)
      ≃⟨ (λ{((xe , xd , pᵣ) , xb , pₗ) → xe , xb , xd , pₗ , pᵣ}) , qinv→isequiv
       ( (λ{(xe , xb , xd , pₗ , pᵣ) → (xe , xd , pᵣ) , xb , pₗ})
       , (λ{((xe , xd , pᵣ) , xb , refl) → refl})
       , (λ{(xe , xb , xd , pₗ , pᵣ) → refl}) ) ⟩
    Σ[ xe ∶ (X → E) ] Σ[ xb ∶ (X → B) ] Σ[ xd ∶ (X → D) ] (xd == bd ∘ xb) × (ef ∘ xe == df ∘ xd)
      ≃⟨ Σ-equiv₂ (λ xe → Σ-equiv₂ λ xb →
        -- Use pₗ to rewrite ef ∘ xe == df ∘ xd as df ∘ bd ∘ xb,
        -- removing the dependency on xd
        Σ[ xd ∶ (X → D) ] (xd == bd ∘ xb) × (ef ∘ xe == df ∘ xd)
          ≃⟨ Σ-equiv₂ (λ xd → Σ-equiv₂ (idtoeqv ∘ ap (λ xf → ef ∘ xe == df ∘ xf))) ⟩
        -- Associate pₗ with xd
        Σ[ xd ∶ (X → D) ] (xd == bd ∘ xb) × (ef ∘ xe == df ∘ bd ∘ xb)
          ≃⟨ Σ-assoc ⟩
        -- Use Lemmas 3.11.8 and 3.11.9 (ii) to contract xd to bd ∘ xb
        (Σ[ xd ∶ (X → D) ] (xd == bd ∘ xb)) × (ef ∘ xe == df ∘ bd ∘ xb)
          ≃⟨ Σ-contr₁ ⦃ =-contrᵣ (bd ∘ xb) ⦄ ⟩
        ef ∘ xe == df ∘ bd ∘ xb
          ∎) ⟩
    pullback (X → E) (X → B) (ef ∘_) ((df ∘ bd) ∘_)
      ∎
    where
    open ≃-Reasoning

  -- Proves that we compose the above equivalence with fₗ, we get out fₒ
  equiv-fₗ→fₒ : {X : 𝒰 i} (xa : X → A) → pr₁ (equiv X) (fₗ xa) == fₒ xa
  equiv-fₗ→fₒ {X = X} xa = pair⁼ (refl , pair⁼ (refl , p))
    where
    xe = ce ∘ ac ∘ xa
    q : (cd ∘ ac ∘ xa , _) == (bd ∘ ab ∘ xa , _)
    q = pair⁼ (funext (commₗ ∘ xa) ⁻¹ , _) ⁻¹
    p : pr₂ (pr₂ (pr₁ (equiv X) (fₗ xa))) == funext (commᵣ ∘ ac ∘ xa ∙ₕ ap df ∘ commₗ ∘ xa)
    p =
      -- Simplify the constant transport
      transport _ q _
        =⟨ transportconst q  _ ⟩
      -- Move the ap function into the transport
      transport id (ap (λ xd → ef ∘ xe == df ∘ xd) (funext (commₗ ∘ xa))) (funext (commᵣ ∘ ac ∘ xa))
        =⟨ transport-ap id (λ xd → ef ∘ xe == df ∘ xd) (funext (commₗ ∘ xa)) (funext (commᵣ ∘ ac ∘ xa)) ⟩
      -- Apply Theorem 2.11.3 to eliminate the transport
      transport (λ xf → ef ∘ xe == df ∘ xf) (funext (commₗ ∘ xa)) (funext (commᵣ ∘ ac ∘ xa))
        =⟨ transport=-constₗ (ef ∘ xe) (df ∘_) (funext (commₗ ∘ xa)) (funext (commᵣ ∘ ac ∘ xa)) ⟩
      -- Combine the ap df into the funext on the right
      funext (commᵣ ∘ ac ∘ xa) ∙ ap (df ∘_) (funext (commₗ ∘ xa))
        =⟨ _ ∙ₗ funext-ap df (commₗ ∘ xa) ⁻¹ ⟩
      -- Combine the two funext
      funext (commᵣ ∘ ac ∘ xa) ∙ funext (ap df ∘ commₗ ∘ xa)
        =⟨ funext-∙ₕ (commᵣ ∘ ac ∘ xa) (ap df ∘ commₗ ∘ xa) ⁻¹ ⟩
      funext (commᵣ ∘ ac ∘ xa ∙ₕ ap df ∘ commₗ ∘ xa)
        ∎
      where open =-Reasoning

  prop₁ : Squareₗ.IsPullback commₗ → Squareₒ.IsPullback commₒ
  prop₁ pullbackₗ X = transport isequiv (funext equiv-fₗ→fₒ) (pr₂ ((fₗ , pullbackₗ X) ∙ₑ equiv X))

  equiv-fₒ→fₗ : {X : 𝒰 i} (xa : X → A) → pr₁ (equiv X ⁻¹ₑ) (fₒ xa) == fₗ xa
  equiv-fₒ→fₗ {X = X} xa = ap g (equiv-fₗ→fₒ xa ⁻¹) ∙ η (fₗ xa)
    where
    open qinv (isequiv→qinv (pr₂ (equiv X)))

  prop₂ : Squareₒ.IsPullback commₒ {i} → Squareₗ.IsPullback commₗ {i}
  prop₂ pullbackₒ X = transport isequiv (funext equiv-fₒ→fₗ) (pr₂ ((fₒ , pullbackₒ X) ∙ₑ equiv X ⁻¹ₑ))

  -- I tried quite hard to come up with the equivalences directly,
  -- but was only able to find one of the four necessary homotopies.
  -- The other three quickly spiraled out of control.

  =pullback-intro : {A B C : 𝒰 i} {ac : A → C} {bc : B → C}
                    {x@(a₁ , b₁ , p) y@(a₂ , b₂ , q) : pullback A B ac bc} →
                    Σ[ p₁ ∶ a₁ == a₂ ] Σ[ p₂ ∶ b₁ == b₂ ] (p ∙ ap bc p₂ == ap ac p₁ ∙ q) → x == y
  =pullback-intro {x = _ , _ , _} {y = _ , _ , _} (refl , refl , p) rewrite unitᵣ ∙ p ∙ unitₗ ⁻¹ = refl

  =pullback-elim : {A B C : 𝒰 i} {ac : A → C} {bc : B → C}
                   {x@(a₁ , b₁ , p) y@(a₂ , b₂ , q) : pullback A B ac bc} →
                   x == y → Σ[ p₁ ∶ a₁ == a₂ ] Σ[ p₂ ∶ b₁ == b₂ ] (p ∙ ap bc p₂ == ap ac p₁ ∙ q)
  =pullback-elim {x = _ , _ , _} {y = _ , _ , _} refl = refl , refl , unitᵣ ⁻¹ ∙ unitₗ

  prop₁' : Squareₗ.IsPullback commₗ → Squareₒ.IsPullback commₒ
  prop₁' pullbackₗ X with isequiv→qinv (pullbackᵣ X) | isequiv→qinv (pullbackₗ X)
  ... | (gᵣ , ηᵣ , εᵣ) | (gₗ , ηₗ , εₗ) = qinv→isequiv (gₒ , ηₒ , εₒ)
    where
    gₒ : pullback (X → E) (X → B) (ef ∘_) ((df ∘ bd) ∘_) → (X → A)
    gₒ (xe , xb , p) = gₗ (gᵣ xc' , xb , ap (pr₁ ∘ pr₂) (εᵣ xc'))
      where
      xc' = (xe , bd ∘ xb , p)

    ηₒ : gₒ ∘ fₒ ~ id
    ηₒ xa = ap gₗ (=pullback-intro (p-xc , refl , p-pₗ)) ∙ ηₗ xa
      where
      pᵣ = funext (commᵣ ∘ ac ∘ xa ∙ₕ ap df ∘ commₗ ∘ xa)
      xc' = ce ∘ ac ∘ xa , bd ∘ ab ∘ xa , pᵣ
      p-xd = funext (commₗ ∘ xa) ⁻¹
      p-pᵣ : pᵣ ∙ ap (df ∘_) p-xd == refl ∙ funext (commᵣ ∘ ac ∘ xa)
      p-pᵣ =
        pᵣ ∙ ap (df ∘_) p-xd                  =⟨ _ ∙ₗ ap-inv (df ∘_) (funext (commₗ ∘ xa)) ⟩
        _ ∙ p ⁻¹                              =⟨ funext-∙ₕ (commᵣ ∘ ac ∘ xa) (ap df ∘ commₗ ∘ xa) ∙ᵣ _  ⟩
        _ ∙ funext (ap df ∘ commₗ ∘ xa) ∙ _   =⟨ _ ∙ₗ funext-ap df (commₗ ∘ xa) ∙ᵣ _ ⟩
        funext (commᵣ ∘ ac ∘ xa) ∙ p ∙ p ⁻¹   =⟨ assoc ⁻¹ ⟩
        funext (commᵣ ∘ ac ∘ xa) ∙ (p ∙ p ⁻¹) =⟨ _ ∙ₗ invᵣ ⟩
        funext (commᵣ ∘ ac ∘ xa) ∙ refl       =⟨ unitᵣ ⁻¹ ⟩
        funext (commᵣ ∘ ac ∘ xa)              =⟨ unitₗ ⟩
        refl ∙ funext (commᵣ ∘ ac ∘ xa)       ∎
        where
        open =-Reasoning
        p = ap (df ∘_) (funext (commₗ ∘ xa))
      p-xc : gᵣ xc' == ac ∘ xa
      p-xc = ap gᵣ (=pullback-intro (refl , p-xd , p-pᵣ)) ∙ ηᵣ (ac ∘ xa)

      -- TODO
      postulate
        p-pₗ : ap (pr₁ ∘ pr₂) (εᵣ xc') ∙ refl == ap (cd ∘_) p-xc ∙ funext (commₗ ∘ xa)

    -- TODO
    postulate
      εₒ : fₒ ∘ gₒ ~ id

  prop₂' : Squareₒ.IsPullback commₒ → Squareₗ.IsPullback commₗ
  prop₂' sₒ-pullback X = qinv→isequiv (gₗ , ηₗ , εₗ)
    where
    open qinv (isequiv→qinv (sₒ-pullback X)) renaming (g to gₒ ; η to ηₒ ; ε to εₒ)
    open qinv (isequiv→qinv (pullbackᵣ X)) renaming (g to gᵣ ; η to ηᵣ ; ε to εᵣ)

    gₗ : pullback (X → C) (X → B) (cd ∘_) (bd ∘_) → (X → A)
    gₗ (xc , xb , pₗ) = gₒ (ce ∘ xc , xb , funext (commᵣ ∘ xc) ∙ ap (df ∘_) pₗ)

    ηₗ : gₗ ∘ fₗ ~ id
    ηₗ xa = ap gₒ (pair⁼ (refl , pair⁼ (refl ,
      _ ∙ₗ funext-ap df (commₗ ∘ xa) ⁻¹ ∙
      funext-∙ₕ (commᵣ ∘ ac ∘ xa) (ap df ∘ commₗ ∘ xa) ⁻¹))) ∙ ηₒ xa

    εₗ : fₗ ∘ gₗ ~ id
    εₗ (xc , xb , pₗ) = =pullback-intro (p-xc , p-xb , p-pₗ)
      where
      xa = gₗ (xc , xb , pₗ)
      xa' = ce ∘ xc , xb , funext (commᵣ ∘ xc) ∙ ap (df ∘_) pₗ
      p-xa' = =pullback-elim (εₒ xa')
      p-xe = pr₁ p-xa'
      p-xb = pr₁ (pr₂ p-xa')
      p-pₒ = pr₂ (pr₂ p-xa')
      p-xd = funext (commₗ ∘ xa) ∙ ap (bd ∘_) p-xb ∙ pₗ ⁻¹
      -- TODO
      postulate
        p-pᵣ : funext (commᵣ ∘ ac ∘ xa) ∙ ap (df ∘_) p-xd == ap (ef ∘_) p-xe ∙ funext (commᵣ ∘ xc)
      p-xc : ac ∘ xa == xc
      p-xc = ηᵣ (ac ∘ xa) ⁻¹ ∙ ap gᵣ (=pullback-intro (p-xe , p-xd , p-pᵣ)) ∙ ηᵣ xc
      -- TODO
      postulate
        p-pₗ : funext (commₗ ∘ xa) ∙ ap (bd ∘_) p-xb == ap (cd ∘_) p-xc ∙ pₗ
