{-# OPTIONS --without-K #-}
open import HoTT.Base

module HoTT.Identity where

open variables
private variable x y z w : A

-- Lemma 2.1.4
--  (i)
unitᵣ : {p : x == y} → p == p ∙ refl
unitᵣ {p = refl} = refl

unitₗ : {p : x == y} → p == refl ∙ p
unitₗ {p = refl} = refl

--  (ii)
invₗ : {p : x == y} → p ⁻¹ ∙ p == refl
invₗ {p = refl} = refl

invᵣ : {p : x == y} → p ∙ p ⁻¹ == refl
invᵣ {p = refl} = refl

--  (iv)
assoc : {p : x == y} {q : y == z} {r : z == w} →
        p ∙ (q ∙ r) == (p ∙ q) ∙ r
assoc {p = refl} {refl} {refl} = refl

invinv : {p : x == y} → p ⁻¹ ⁻¹ == p
invinv {p = refl} = refl

-- Whiskering
_∙ᵣ_ : {p q : x == y} (α : p == q) (r : y == z) → p ∙ r == q ∙ r
refl ∙ᵣ refl = refl
infixl 25 _∙ᵣ_

_∙ₗ_ : {r s : y == z} (q : x == y) (β : r == s) → q ∙ r == q ∙ s
refl ∙ₗ refl = refl
infixl 25 _∙ₗ_

-- Horizontal composition
_⋆_ : {p q : x == y} {r s : y == z} → (p == q) → (r == s) → p ∙ r == q ∙ s
refl ⋆ refl = refl

cancelᵣ : {p q : x == y} {r : y == z} (α : p ∙ r == q ∙ r) → p == q
cancelᵣ {r = refl} α = unitᵣ ∙ α ∙ unitᵣ ⁻¹

cancelₗ : {r s : y == z} {q : x == y} (β : q ∙ r == q ∙ s) → r == s
cancelₗ {q = refl} β = unitₗ ∙ β ∙ unitₗ ⁻¹

pivotᵣ : {p : x == y} {q : y == z} {r : x == z} → p ∙ q == r → p == r ∙ q ⁻¹
pivotᵣ {p = refl} {q = refl} α = α ∙ unitᵣ

pivotₗ : {p : x == y} {q : y == z} {r : x == z} → p ∙ q == r → q == p ⁻¹ ∙ r
pivotₗ {p = refl} {q = refl} α = α ∙ unitₗ

-- Lemma 2.2.2
--  (i)
ap-∙ : (f : A → B) (p : x == y) (q : y == z) → ap f (p ∙ q) == ap f p ∙ ap f q
ap-∙ _ refl refl = refl

--  (ii)
ap-inv : (f : A → B) (p : x == y) → ap f (p ⁻¹) == ap f p ⁻¹
ap-inv _ refl = refl

--  (iii)
ap-∘ : {C : 𝒰 i} (f : B → C) (g : A → B) (p : x == y) → ap (f ∘ g) p == ap f (ap g p)
ap-∘ _ _ refl = refl

--  (iv)
ap-id : (p : x == y) → ap id p == p
ap-id refl = refl

ap-const : (p : x == y) → ap (const B) p == refl
ap-const refl = refl

-- Lemma 2.3.5
transportconst : (p : x == y) → transport (const B) p ~ id
transportconst refl _ = refl

-- Lemma 2.3.9
transport-∙ : (P : A → 𝒰 i) (p : x == y) (q : y == z) →
              transport P (p ∙ q) ~ transport P q ∘ transport P p
transport-∙ P refl refl _ = refl

-- Lemma 2.3.10
transport-ap : (P : B → 𝒰 i) (f : A → B) {x y : A} (p : x == y) →
               transport P (ap f p) ~ transport (P ∘ f) p
transport-ap _ _ refl _ = refl

-- Lemma 2.3.11
transport-∘ : (f : {x : A} → P x → Q x) (p : x == y) →
              transport Q p ∘ f ~ f ∘ transport P p
transport-∘ _ refl _ = refl

module =-Reasoning {i} {A : 𝒰 i}
  where
  _=⟨_⟩_ : (x : A) {y z : A} → x == y → y == z → x == z
  x =⟨ p ⟩ q = p ∙ q
  infixr 2 _=⟨_⟩_

  _=⟨⟩_ : (x : A) {y : A} → x == y → x == y
  _ =⟨⟩ p = p
  infixr 2 _=⟨⟩_

  _∎ : (x : A) → x == x
  _ ∎ = refl
  infix 3 _∎
