{-# OPTIONS --without-K #-}
module HoTT.NaturalNumber where

open import HoTT.Base renaming (_+_ to _⊎_)
open import HoTT.Identity

private variable n m : ℕ

_+_ : ℕ → ℕ → ℕ
0 + m = m
succ n + m = succ (n + m)

+-comm : (n m : ℕ) → n + m == m + n
+-comm zero zero = refl
+-comm zero (succ m) = ap succ (+-comm zero m)
+-comm (succ n) zero = ap succ (+-comm n zero)
+-comm (succ n) (succ m) = ap succ $
  n + succ m   =⟨ +-comm n (succ m) ⟩
  succ m + n   =⟨ ap (succ) (+-comm m n) ⟩
  succ (n + m) =⟨ +-comm (succ n) m ⟩
  m + succ n   ∎
  where open =-Reasoning

_≤_ : ℕ → ℕ → 𝒰₀
n ≤ m = Σ ℕ λ k → n + k == m

≤succ : n ≤ m → n ≤ succ m
≤succ {n} (k , p) = succ k , +-comm n (succ k) ∙ ap succ (+-comm k n ∙ p)

_<_ : ℕ → ℕ → 𝒰₀
n < m = succ n ≤ m

_<=>_ : (n m : ℕ) → (n == m) ⊎ (n < m) ⊎ (m < n)
zero <=> zero = inl refl
zero <=> succ m = inr (inl (m , refl))
succ n <=> zero = inr (inr (n , refl))
succ n <=> succ m with n <=> m
... | inl p = inl (ap succ p)
... | inr (inl (k , p)) = inr (inl (k , ap succ p))
... | inr (inr (k , p)) = inr (inr (k , ap succ p))
