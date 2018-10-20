module HoTT.Coproduct where

open import HoTT.Types
open import HoTT.Equivalence
open import HoTT.Homotopy
open import HoTT.Identity using (ap ; transport)

+-rec : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
        (C : 𝒰 k) → (A → C) → (B → C) → A + B → C
+-rec C g₀ g₁ (inl a) = g₀ a
+-rec C g₀ g₁ (inr b) = g₁ b

+-ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
        (C : A + B → 𝒰 k) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
+-ind C g₀ g₁ (inl a) = g₀ a
+-ind C g₀ g₁ (inr b) = g₁ b

code : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} (x y : A + B) → 𝒰 (i ⊔ j)
code {i} {j} (inl a₁) (inl a₂) = Lift {j} (a₁ == a₂)
code (inl _) (inr _) = Lift 𝟎
code {i} {j} (inr b₁) (inr b₂) = Lift {i} (b₁ == b₂)
code (inr _) (inl _) = Lift 𝟎

encode : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} {x y : A + B} → x == y → code x y
encode {i} {A} {B} {inl a} p = transport {A = A + B} {code (inl a)} p (lift refl)
encode {i} {A} {B} {inr b} p = transport {A = A + B} {code (inr b)} p (lift refl)

decode : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} {x y : A + B} → code x y → x == y
decode {x = inl _} {inl _} (lift p) = ap inl p
decode {x = inl _} {inr _} ()
decode {x = inr _} {inr _} (lift p) = ap inr p
decode {x = inr _} {inl _} ()

+-identity : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} {x y : A + B} →
             (x == y) ≃ code x y
+-identity {A = A} {B} {x} {y} = encode , qinv→isequiv (decode , α {x} , β)
  where
    α : {x y : A + B} → encode {x = x} {y} ∘ decode ~ id
    α {inl _} {inl _} (lift p) rewrite p = refl
    α {inl _} {inr _} (lift ())
    α {inr _} {inl _} (lift ())
    α {inr _} {inr _} (lift p) rewrite p = refl
    β : {x y : A + B} → decode {x = x} {y} ∘ encode ~ id
    β {y = inl a} p rewrite p = refl
    β {y = inr b} p rewrite p = refl
