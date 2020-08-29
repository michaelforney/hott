{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Equivalence
open import HoTT.Identity

module HoTT.Identity.NaturalNumber where

private variable m n : ℕ

_=ℕ_ : ℕ → ℕ → 𝒰₀
zero =ℕ zero = 𝟏
zero =ℕ (succ _) = 𝟎
succ _ =ℕ zero = 𝟎
succ m =ℕ succ n = m =ℕ n

private
  r : (n : ℕ) → n =ℕ n
  r zero = ★
  r (succ n) = r n

=ℕ-elim : m == n → m =ℕ n
=ℕ-elim {m} p = transport (m =ℕ_) p (r m)

=ℕ-intro : m =ℕ n → m == n
=ℕ-intro {zero} {zero} _ = refl
=ℕ-intro {zero} {succ n} ()
=ℕ-intro {succ m} {zero} ()
=ℕ-intro {succ m} {succ n} = ap succ ∘ =ℕ-intro

=ℕ-equiv : {m n : ℕ} → m == n ≃ m =ℕ n
=ℕ-equiv {x} = f , qinv→isequiv (g , η , ε {x})
  where
  f = =ℕ-elim
  g = =ℕ-intro

  η : g ∘ f {m} {n} ~ id
  η {zero} refl = refl
  η {succ n} refl = ap (ap succ) (η refl)

  ε : f ∘ g {m} {n} ~ id
  ε {zero} {zero} ★ = refl
  ε {zero} {succ n} ()
  ε {succ m} {zero} ()
  ε {succ m} {succ n} p = transport-ap (succ m =ℕ_) succ (g p) (r m) ∙ ε {m} p
