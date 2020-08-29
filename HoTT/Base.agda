{-# OPTIONS --without-K #-}
module HoTT.Base where

open import Agda.Primitive public

-- Universe
𝒰 : (i : Level) → Set (lsuc i)
𝒰 i = Set i

𝒰₀ : Set₁
𝒰₀ = Set₀

module variables where
  variable
    i j : Level
    A B : 𝒰 i
    P Q : A → 𝒰 i
open variables

record Lift {i j} (A : 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor lift
  field lower : A
open Lift public

-- Instance search
⟨⟩ : ∀ {i} {A : 𝒰 i} → ⦃ A ⦄ → A
⟨⟩ ⦃ a ⦄ = a

-- Dependent functions (Π-types)
Π : (A : 𝒰 i) (B : A → 𝒰 j) → 𝒰 (i ⊔ j)
Π A B = (x : A) → B x
syntax Π A (λ x → Φ) = Π[ x ∶ A ] Φ
infixr 6 Π

id : {A : 𝒰 i} → A → A
id x = x

const : A → B → A
const x _ = x

swap : {C : A → B → 𝒰 i} → ((x : A) (y : B) → C x y) →
       (y : B) (x : A) → C x y
swap f y x = f x y

_∘_ : {C : {x : A} → P x → 𝒰 i} →
      ({x : A} → Π (P x) C) → (g : Π A P) → (x : A) → C (g x)
f ∘ g = λ x → f (g x)
infixr 30 _∘_

_$_ : Π A P → Π A P
_$_ = id
infixr 0 _$_

-- Identity
data _==_ {A : 𝒰 i} (a : A) : A → 𝒰 i where
  instance refl : a == a
infixr 10 _==_
{-# BUILTIN EQUALITY _==_ #-}

=-ind : (C : (x y : A) → x == y → 𝒰 i) → ((x : A) → C x x refl) →
        {x y : A} → (p : x == y) → C x y p
=-ind C c refl = c _

-- Based path induction
=-ind' : {a : A} → (C : (x : A) → a == x → 𝒰 i) → C a refl →
         {x : A} → (p : a == x) → C x p
=-ind' C c refl = c

-- Lemma 2.1.1
_⁻¹ : {x y : A} → x == y → y == x
_⁻¹ refl = refl
infix 30 _⁻¹

-- Lemma 2.1.2
_∙_ : {x y z : A} → x == y → y == z → x == z
_∙_ refl refl = refl
infixl 20 _∙_

-- Lemma 2.2.1
ap : {x y : A} (f : A → B) → x == y → f x == f y
ap f refl = refl

ap² : {C : 𝒰 i} {x y : A} {z w : B} (f : A → B → C) → x == y → z == w → f x z == f y w
ap² _ refl refl = refl

-- Lemma 2.3.1
transport : {x y : A} (P : A → 𝒰 j) → x == y → P x → P y
transport _ refl = id

-- Lemma 2.3.4
apd : {x y : A} (f : (x : A) → P x) (p : x == y) → transport P p (f x) == f y
apd f refl = refl

-- Empty
data 𝟎 {i} : 𝒰 i where

𝟎-rec : {C : 𝒰 i} → 𝟎 {j} → C
𝟎-rec ()

𝟎-ind : {C : 𝟎 → 𝒰 i} → (z : 𝟎 {j}) → C z
𝟎-ind ()

¬_ : 𝒰 i → 𝒰 i
¬_ {i} A = A → 𝟎 {i}
infix 25 ¬_

_≠_ : A → A → 𝒰 _
_≠_ x y = ¬ (x == y)

-- Unit
record 𝟏 {i} : 𝒰 i where
  no-eta-equality
  instance constructor ★

𝟏-ind : (C : 𝟏 → 𝒰 i) → C ★ → (x : 𝟏 {j}) → C x
𝟏-ind C c ★ = c

𝟏-uniq : (x : 𝟏 {i}) → x == ★
𝟏-uniq ★ = refl

-- Boolean
data 𝟐 : 𝒰₀ where
  0₂ : 𝟐
  1₂ : 𝟐
{-# BUILTIN BOOL 𝟐 #-}
{-# BUILTIN FALSE 0₂ #-}
{-# BUILTIN TRUE 1₂ #-}

𝟐-rec : {C : 𝒰 i} → C → C → 𝟐 → C
𝟐-rec c₀ c₁ 0₂ = c₀
𝟐-rec c₀ c₁ 1₂ = c₁

𝟐-ind : (C : 𝟐 → 𝒰 i) → C 0₂ → C 1₂ → (x : 𝟐) → C x
𝟐-ind C c₀ c₁ 0₂ = c₀
𝟐-ind C c₀ c₁ 1₂ = c₁

-- Dependent pairs (Σ-types)
record Σ (A : 𝒰 i) (B : A → 𝒰 j) : 𝒰 (i ⊔ j) where
  no-eta-equality
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
infixr 15 _,_
open Σ public
syntax Σ A (λ x → Φ) = Σ[ x ∶ A ] Φ
infixr 6 Σ

Σ-rec : (C : 𝒰 i) → ((x : A) → P x → C) → (Σ A λ x → P x) → C
Σ-rec C g (a , b) = g a b

Σ-ind : (C : Σ A P → 𝒰 i) → ((a : A) → (b : P a) → C (a , b)) →
        (p : Σ A P) → C p
Σ-ind C g (a , b) = g a b

Σ-uniq : (x : Σ A P) → pr₁ x , pr₂ x == x
Σ-uniq (a , b) = refl

-- Product
_×_ : (A : 𝒰 i) (B : 𝒰 j) → 𝒰 (i ⊔ j)
A × B = Σ[ _ ∶ A ] B
infixr 8 _×_

×-rec : (C : 𝒰 i) → (A → B → C) → A × B → C
×-rec _ g (a , b) = g a b

×-ind : (C : A × B → 𝒰 i) → ((x : A) (y : B) → C (x , y)) →
        (x : A × B) → C x
×-ind _ g (a , b) = g a b

×-uniq : (x : A × B) → pr₁ x , pr₂ x == x
×-uniq (a , b) = refl

-- Coproduct
data _+_ (A : 𝒰 i) (B : 𝒰 j) : 𝒰 (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B
infixr 8 _+_

+-rec : {C : 𝒰 i} → (A → C) → (B → C) → A + B → C
+-rec gₗ gᵣ (inl a) = gₗ a
+-rec gₗ gᵣ (inr b) = gᵣ b

+-ind : (C : A + B → 𝒰 i) →
        ((a : A) → C (inl a)) →
        ((b : B) → C (inr b)) → (x : A + B) → C x
+-ind C g₀ g₁ (inl a) = g₀ a
+-ind C g₀ g₁ (inr b) = g₁ b

-- Natural numbers
data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

ℕ-rec : {C : 𝒰 i} → C → (ℕ → C → C) → ℕ → C
ℕ-rec c₀ cₛ zero = c₀
ℕ-rec c₀ cₛ (succ n) = cₛ n (ℕ-rec c₀ cₛ n)

ℕ-ind : (C : ℕ → 𝒰 i) → C 0 → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
ℕ-ind C c₀ cₛ 0 = c₀
ℕ-ind C c₀ cₛ (succ n) = cₛ n (ℕ-ind C c₀ cₛ n)

-- Homotopy
_~_ : (f g : Π A P) → 𝒰 _
f ~ g = ∀ x → f x == g x

happly : {f g : Π A P} → f == g → f ~ g
happly refl _ = refl

-- Lemma 2.4.2
reflₕ : {f : Π A P} → f ~ f
reflₕ _ = refl

_∙ₕ_ : {f g h : Π A P} → f ~ g → g ~ h → f ~ h
α ∙ₕ β = λ x → α x ∙ β x
infixl 20 _∙ₕ_

_⁻¹ₕ : {f g : Π A P} → f ~ g → g ~ f
α ⁻¹ₕ = λ x → α x ⁻¹
