{-# OPTIONS --without-K #-}
module HoTT.Types where

open import Agda.Primitive public

-- Universe
𝒰 : (i : Level) → Set (lsuc i)
𝒰 i = Set i

𝒰₀ : Set₁
𝒰₀ = Set

record Lift {i j} (A : 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor lift
  field lower : A
open Lift public

-- Pi
Π : ∀ {i j} (A : 𝒰 i) (B : A → 𝒰 j) → 𝒰 (i ⊔ j)
Π A B = (x : A) → B x

id : ∀ {i} {A : 𝒰 i} → A → A
id x = x

const : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A → B → A
const x _ = x

_∘_ : ∀ {i j k} {A : 𝒰 i} {B : A → 𝒰 j} {C : {x : A} → B x → 𝒰 k} →
      ({x : A} → Π (B x) C) → (g : Π A B) → (x : A) → C (g x)
f ∘ g = λ x → f (g x)
infixr 30 _∘_

-- Empty
data 𝟎 : 𝒰₀ where

-- Unit
record 𝟏 : 𝒰₀ where
  constructor ★

-- Boolean
data 𝟐 : 𝒰₀ where
  0₂ : 𝟐
  1₂ : 𝟐
{-# BUILTIN BOOL 𝟐 #-}
{-# BUILTIN FALSE 0₂ #-}
{-# BUILTIN TRUE 1₂ #-}

-- Natural number
data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Sigma
record Σ {i j} (A : 𝒰 i) (B : A → 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
infixr 15 _,_
open Σ public

-- Product
_×_ : ∀ {i j} (A : 𝒰 i) (B : 𝒰 j) → 𝒰 (i ⊔ j)
A × B = Σ A λ _ → B

-- Coproduct
data _+_ {i j} (A : 𝒰 i) (B : 𝒰 j) : 𝒰 (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

-- Identity
data _==_ {i} {A : 𝒰 i} (a : A) : A → 𝒰 i where
  refl : a == a
infixr 10 _==_
{-# BUILTIN EQUALITY _==_ #-}

-- Homotopy
_~_ : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} (f g : Π A P) → 𝒰 (i ⊔ j)
_~_ {A = A} f g = (x : A) → f x == g x

-- Equivalence
qinv : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} (f : A → B) → 𝒰 (i ⊔ j)
qinv {A = A} {B} f = Σ (B → A) λ g → (f ∘ g ~ id) × (g ∘ f ~ id)

isequiv : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} (f : A → B) → 𝒰 (i ⊔ j)
isequiv {_} {_} {A} {B} f = (Σ (B → A) λ g → f ∘ g ~ id) × (Σ (B → A) λ h → h ∘ f ~ id)

_≃_ : ∀ {i j} (A : 𝒰 i) (B : 𝒰 j) → 𝒰 (i ⊔ j)
A ≃ B = Σ (A → B) λ f → isequiv f
