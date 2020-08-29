{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Equivalence.Lift
open import HoTT.Identity.Sigma
open import HoTT.Identity.Universe
open import HoTT.HLevel
open import HoTT.Logic

module HoTT.Exercises.Chapter3.Exercise10 {i} where

postulate
  lem : LEM {lsuc i}

_ : Prop𝒰 i ≃ Prop𝒰 (lsuc i)
_ = f , qinv→isequiv (g , η , ε)
  where
  f : _
  f P = LiftProp P
  g : _
  g P with lem P
  ... | inl _ = ⊤
  ... | inr _ = ⊥
  η : g ∘ f ~ id
  η P with lem (f P)
  ... | inl t = hlevel⁼ (ua (prop-equiv (const (lower t)) (const ★)))
  ... | inr f = hlevel⁼ (ua (prop-equiv 𝟎-rec (𝟎-rec ∘ f ∘ lift)))
  ε : f ∘ g ~ id
  ε P with lem P
  ... | inl t = hlevel⁼ (ua (Lift-equiv ∙ₑ prop-equiv (const t) (const ★)))
  ... | inr f = hlevel⁼ (ua (Lift-equiv ∙ₑ prop-equiv 𝟎-rec (𝟎-rec ∘ f)))
