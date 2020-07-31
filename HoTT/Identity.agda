{-# OPTIONS --without-K #-}
module HoTT.Identity where

open import HoTT.Types
open import HoTT.Empty using (¬_)

=-ind : ∀ {i j} {A : 𝒰 i} →
        (C : (x y : A) → x == y → 𝒰 j) → ((x : A) → C x x refl) → (x y : A) → (p : x == y) → C x y p
=-ind C c x .x refl = c x

-- Based path induction
=-ind' : ∀ {i j} {A : 𝒰 i} →
         (a : A) → (C : (x : A) → a == x → 𝒰 j) → C a refl → (x : A) → (p : a == x) → C x p
=-ind' a C c .a refl = c

_≠_ : ∀ {i} {A : 𝒰 i} → A → A → 𝒰 i
_≠_ x y = ¬ (x == y)

-- Lemma 2.1.1
_⁻¹ : ∀ {i} {A : 𝒰 i} {x y : A} → x == y → y == x
_⁻¹ refl = refl
infix 30 _⁻¹

{- Induction proof
_⁻¹ {i} {A} {x} {y} p = =-ind D d x y p
  where
    D : (x y : A) → x == y → 𝒰 i
    D x y p = y == x
    d : (x : A) → D x x refl
    d x = refl
-}

-- Lemma 2.1.2
_∙_ : ∀ {i} {A : 𝒰 i} {x y z : A} → x == y → y == z → x == z
_∙_ refl refl = refl
infixl 20 _∙_

{- Induction proof
_∙_ {i} {A} {x} {y} {z} p q = =-ind D d x y p z q where
  E : (x z : A) (q : x == z) → 𝒰 i
  E x z q = x == z
  e : (x : A) → E x x refl
  e x = refl
  D : (x y : A) → x == y → 𝒰 i
  D x y p = (z : A) (q : y == z) → x == z
  d : (x : A) → D x x refl
  d x z q = =-ind E e x z q
-}

-- Lemma 2.1.4
--  (i)
ru : ∀ {i} {A : 𝒰 i} {x y : A} (p : x == y) → p == p ∙ refl
ru {x = x} {y} p = =-ind (λ _ _ p → p == p ∙ refl) (λ _ → refl) x y p

lu : ∀ {i} {A : 𝒰 i} {x y : A} (p : x == y) → p == refl ∙ p
lu {x = x} {y} p = =-ind (λ _ _ p → p == refl ∙ p) (λ _ → refl) x y p

--  (ii)
=-linv : ∀ {i} {A : 𝒰 i} {x y : A} (p : x == y) → p ⁻¹ ∙ p == refl
=-linv {x = x} {y} p = =-ind (λ _ _ p → p ⁻¹ ∙ p == refl) (λ _ → refl) x y p

=-rinv : ∀ {i} {A : 𝒰 i} {x y : A} (p : x == y) → p ∙ p ⁻¹ == refl
=-rinv {x = x} {y} p = =-ind (λ _ _ p → p ∙ p ⁻¹ == refl) (λ _ → refl) x y p

--  (iv)
assoc : ∀ {i} {A : 𝒰 i} {x y z w : A} (p : x == y) (q : y == z) (r : z == w) →
        p ∙ (q ∙ r) == (p ∙ q) ∙ r
assoc refl refl refl = refl

{- Induction proof
assoc {i} {A} {x} {y} {z} {w} p q r = =-ind D₁ d₁ x y p z w q r where
  D₃ : (z w : A) → (r : z == w) → 𝒰 i
  D₃ _ _ r = refl ∙ (refl ∙ r) == (refl ∙ refl) ∙ r
  d₃ : (z : A) → D₃ z z refl
  d₃ _ = refl

  D₂ : (y z : A) → (q : y == z) → 𝒰 i
  D₂ _ z q = (w : A) → (r : z == w) → refl ∙ (q ∙ r) == (refl ∙ q) ∙ r
  d₂ : (z : A) → D₂ z z refl
  d₂ z w r = =-ind D₃ d₃ z w r

  D₁ : (x y : A) → (p : x == y) → 𝒰 i
  D₁ _ y p = (z w : A) → (q : y == z) → (r : z == w) → p ∙ (q ∙ r) == (p ∙ q) ∙ r
  d₁ : (y : A) → D₁ y y refl
  d₁ y z w q r = =-ind D₂ d₂ y z q w r
-}

-- Lemma 2.2.1
ap : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A}
     (f : A → B) → x == y → f x == f y
ap f refl = refl

{- Induction proof
ap {x = x} {y} f p = =-ind (λ x y _ → f x == f y) (λ _ → refl) x y p
-}

-- Lemma 2.3.1
transport : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} {x y : A} →
            x == y → P x → P y
transport refl = id

{- Induction proof
transport {P = P} {x} {y} p = =-ind (λ x y _ → P x → P y) (λ _ → id) x y p
-}

-- Lemma 2.3.4
apd : ∀ {i j} {A : 𝒰 i} {P : A → 𝒰 j} {x y : A}
      (f : (x : A) → P x) (p : x == y) → transport p (f x) == f y
apd f refl = refl

{- Induction proof
apd {x = x} {y} f p = =-ind (λ x y p → transport p (f x) == f y) (λ _ → refl) x y p
-}

-- Lemma 2.3.5
transportconst : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A}
                 (p : x == y) (b : B) → transport p b == b
transportconst refl _ = refl
