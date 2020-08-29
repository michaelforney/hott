{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.HLevel
open import HoTT.HLevel.Truncate
open import HoTT.Logic
open import HoTT.Identity
open import HoTT.Identity.Identity
open import HoTT.Identity.Coproduct
open import HoTT.Identity.Sigma
open import HoTT.Identity.Pi
open import HoTT.Identity.Universe
open import HoTT.Equivalence
open import HoTT.Equivalence.Lift
open import HoTT.Sigma.Transport

module HoTT.Exercises.Chapter3 where

module Exercise1 {i} {A B : 𝒰 i} (e : A ≃ B) (A-set : isSet A)
  where
  □ : isSet B
  □ {x} {y} p q = ap⁻¹ (ap≃ (e ⁻¹ₑ) x y) (A-set (ap g p) (ap g q))
    where open Iso (eqv→iso e)

module Exercise2 {i} {A B : 𝒰 i} (A-set : isSet A) (B-set : isSet B)
  where
  □ : isSet (A + B)
  □ {inl x} {inl y} p q = ap⁻¹ =+-equiv
    (ap lift (A-set (lower (=+-elim p)) (lower (=+-elim q))))
  □ {inl x} {inr y} p q = 𝟎-rec (=+-elim p)
  □ {inr x} {inl y} p q = 𝟎-rec (=+-elim p)
  □ {inr x} {inr y} p q = ap⁻¹ =+-equiv
    (ap lift (B-set (lower (=+-elim p)) (lower (=+-elim q))))

module Exercise3
  {i} {A : 𝒰 i} (A-set : isSet A)
  {j} {B : A → 𝒰 j} (B-set : {x : A} → isSet (B x))
  where
  □ : isSet (Σ A B)
  □ {x = x@(x₁ , x₂)} {y = y@(y₁ , y₂)} p q =
    ap⁻¹ =Σ-equiv (lemma (pr₁ =Σ-equiv p) (pr₁ =Σ-equiv q))
    where
    lemma : (p q : Σ (x₁ == y₁) λ p₁ → (transport B p₁ x₂ == y₂)) → p == q
    lemma (p₁ , p₂) (q₁ , q₂) = pair⁼ (r₁ , r₂)
      where
      r₁ = A-set p₁ q₁
      r₂ = B-set (transport _ r₁ p₂) q₂

module Exercise4 {i} {A : 𝒰 i} where
  _ : isProp A → isContr (A → A)
  _ = λ A-prop → id , λ f → funext λ x → A-prop x (f x)

  _ : isContr (A → A) → isProp A
  _ = λ where
      (f , contr) x y → happly (contr (const x) ⁻¹ ∙ contr (const y)) x

module Exercise5 {i} {A : 𝒰 i} where
  open import HoTT.Pi.Transport
  open import HoTT.Sigma.Transport

  _ : isProp A ≃ (A → isContr A)
  _ = f , qinv→isequiv (g , η , ε)
    where
    f : isProp A → (A → isContr A)
    f A-prop x = x , A-prop x
    g : (A → isContr A) → isProp A
    g h x y = let contr = pr₂ (h x) in contr x ⁻¹ ∙ contr y
    η : g ∘ f ~ id
    η _ = isProp-prop _ _
    ε : f ∘ g ~ id
    ε h = funext λ _ → isContr-prop _ _

module Exercise6 {i} {A : 𝒰 i} where
  instance
    LEM-prop : ⦃ hlevel 1 A ⦄ → hlevel 1 (A + ¬ A)
    LEM-prop = isProp→hlevel1 λ where
      (inl a) (inl a') → ap inl center
      (inl a) (inr f) → 𝟎-rec (f a)
      (inr f) (inl b') → 𝟎-rec (f b')
      (inr f) (inr f') → ap inr center

module Exercise7
  {i} {A : 𝒰 i} {A-prop : isProp A}
  {j} {B : 𝒰 j} {B-prop : isProp B}
  where
  □ : ¬ (A × B) → isProp (A + B)
  □ f = λ where
      (inl x) (inl y) → ap inl (A-prop _ _)
      (inl x) (inr y) → 𝟎-rec (f (x , y))
      (inr x) (inl y) → 𝟎-rec (f (y , x))
      (inr x) (inr y) → ap inr (B-prop _ _)

module Exercise8 {i j} {A : 𝒰 i} {B : 𝒰 j} {f : A → B} where
  open import HoTT.Equivalence.Proposition
  prop₁ : qinv f → ∥ qinv f ∥
  prop₁ e = ∣ e ∣
  prop₂ : ∥ qinv f ∥ → qinv f
  prop₂ e = isequiv→qinv (∥-rec ⦃ isProp→hlevel1 isequiv-prop ⦄ qinv→isequiv e)
  prop₃ : isProp ∥ qinv f ∥
  prop₃ = hlevel1→isProp

module Exercise9 {i} (lem : LEM {i}) where
  open import HoTT.Logic
  open import HoTT.Equivalence.Lift

  _ : Prop𝒰 i ≃ 𝟐
  _ = f , qinv→isequiv (g , η , ε)
    where
    f : Prop𝒰 i → 𝟐
    f P with lem P
    ... | inl _ = 0₂
    ... | inr _ = 1₂
    g : 𝟐 → Prop𝒰 i
    g 0₂ = ⊤
    g 1₂ = ⊥
    η : g ∘ f ~ id
    η P with lem P
    ... | inl t = hlevel⁼ (ua (prop-equiv (const t) (const ★)))
    ... | inr f = hlevel⁼ (ua (prop-equiv 𝟎-rec (𝟎-rec ∘ f)))
    ε : f ∘ g ~ id
    ε 0₂ with lem (g 0₂)
    ... | inl _ = refl
    ... | inr f = 𝟎-rec (f ★)
    ε 1₂ with lem (g 1₂)
    ... | inl ()
    ... | inr _ = refl

import HoTT.Exercises.Chapter3.Exercise10

module Exercise11 where
  open variables
  open import HoTT.Pi.Transport
  open import HoTT.Identity.Boolean

  prop : ¬ ((A : 𝒰₀) → ∥ A ∥ → A)
  prop f = 𝟎-rec (g (f 𝟐 ∣ 0₂ ∣) p)
    where
    not = 𝟐-rec 1₂ 0₂
    e : 𝟐 ≃ 𝟐
    e = not , qinv→isequiv (not , 𝟐-ind _ refl refl , 𝟐-ind _ refl refl)
    g : (x : 𝟐) → ¬ (not x == x)
    g 0₂ = 𝟎-rec ∘ pr₁ =𝟐-equiv
    g 1₂ = 𝟎-rec ∘ pr₁ =𝟐-equiv
    p : not (f 𝟐 ∣ 0₂ ∣) == f 𝟐 ∣ 0₂ ∣
    p =
      not (f 𝟐 ∣ 0₂ ∣)
        =⟨ ap (λ e → pr₁ e (f 𝟐 ∣ 0₂ ∣)) (=𝒰-β e) ⁻¹ ⟩
      transport id (ua e) (f 𝟐 ∣ 0₂ ∣)
        =⟨ ap (λ x → transport id (ua e) (f 𝟐 x)) center ⟩
      transport id (ua e) (f 𝟐 (transport ∥_∥ (ua e ⁻¹) ∣ 0₂ ∣))
        =⟨ happly (transport-→ ∥_∥ id (ua e) (f 𝟐) ⁻¹) ∣ 0₂ ∣ ⟩
      transport (λ A → ∥ A ∥ → A) (ua e) (f 𝟐) ∣ 0₂ ∣
        =⟨ happly (apd f (ua e)) ∣ 0₂ ∣ ⟩
      f 𝟐 ∣ 0₂ ∣
        ∎
      where open =-Reasoning

module Exercise12 {i} {A : 𝒰 i} (lem : LEM {i}) where
  open variables using (B ; j)

  □ : ∥ (∥ A ∥ → A) ∥
  □ with lem (type ∥ A ∥)
  ... | inl x = swap ∥-rec x λ x → ∣ const x ∣
  ... | inr f = ∣ 𝟎-rec ∘ f ∣

module Exercise13 {i} (lem : LEM∞ {i}) where
  □ : AC {i} {i} {i}
  □ {X = X} {A = A} {P = P} f = ∣ pr₁ ∘ g , pr₂ ∘ g ∣
    where
    g : (x : X) → Σ (A x) (P x)
    g x with lem (Σ (A x) (P x))
    ... | inl t = t
    ... | inr b = ∥-rec ⦃ hlevel-in (λ {x} → 𝟎-rec (b x)) ⦄ id (f x)

module Exercise14 (lem : ∀ {i} → LEM {i}) where
  open import HoTT.Sigma.Universal

  open variables

  ∥_∥' : 𝒰 i → 𝒰 i
  ∥ A ∥' = ¬ ¬ A

  ∣_∣' : A → ∥ A ∥'
  ∣ a ∣' f = f a

  ∥'-hlevel : hlevel 1 ∥ A ∥'
  ∥'-hlevel = ⟨⟩

  ∥'-rec : ⦃ hlevel 1 B ⦄ → (f : A → B) →
           Σ[ g ∶ (∥ A ∥' → B) ] Π[ a ∶ A ] g ∣ a ∣' == f a
  ∥'-rec f = λ where
    .pr₁ a → +-rec id (λ b → 𝟎-rec (a (𝟎-rec ∘ b ∘ f))) (lem (type _))
    .pr₂ _ → center

  _ : ∥ A ∥' ≃ ∥ A ∥
  _ = let open Iso in iso→eqv λ where
    .f → pr₁ (∥'-rec ∣_∣)
    .g → ∥-rec ∣_∣'
    .η _ → center
    .ε _ → center

module Exercise15
  (LiftProp-isequiv : ∀ {i j} → isequiv (LiftProp {i} {j}))
  where
  open import HoTT.Equivalence.Transport
  open variables

  open module LiftProp-qinv {i} {j} = qinv (isequiv→qinv (LiftProp-isequiv {i} {j}))
    renaming (g to LowerProp ; η to LiftProp-η ; ε to LiftProp-ε)

  ∥_∥' : 𝒰 (lsuc i) → 𝒰 (lsuc i)
  ∥_∥' {i} A = (P : Prop𝒰 i) → (A → P ty) → P ty

  ∣_∣' : A → ∥ A ∥'
  ∣ a ∣' _ f = f a

  ∥'-hlevel : hlevel 1 ∥ A ∥'
  ∥'-hlevel = ⟨⟩

  ∥'-rec : {A : 𝒰 (lsuc i)} {(type B) : Prop𝒰 (lsuc i)} → (f : A → B) →
           Σ (∥ A ∥' → B) λ g → (a : A) → g ∣ a ∣' == f a
  ∥'-rec {_} {_} {B} f = let p = ap _ty (LiftProp-ε B) in λ where
    .pr₁ a → transport id p (lift (a (LowerProp B) (lower ∘ transport id (p ⁻¹) ∘ f)))
    -- We do not get a definitional equality since our propositional
    -- resizing equivalence does not give us definitionally equal
    -- types, i.e. LowerProp B ‌≢ B. If it did, then we could write
    --
    --   ∥'-rec f a :≡ a (LowerProp B) f
    --
    -- and then we'd have ∥'-rec f ∣a∣' ≡ f a.
    .pr₂ a → Eqv.ε (transport-equiv p) (f a)

module Exercise16
  {i} {(type X) : Set𝒰 i}
  {j} {Y : X → Prop𝒰 j}
  (lem : ∀ {i} → LEM {i})
  where
  _ : Π[ x ∶ X ] ¬ ¬ Y x ty ≃ ¬ ¬ (Π[ x ∶ X ] Y x ty)
  _ = let open Iso in iso→eqv λ where
    .f s t → t λ x → +-rec id (𝟎-rec ∘ s x) (lem (Y x))
    .g s x y → 𝟎-rec (s λ f → 𝟎-rec (y (f x)))
    .η _ → center
    .ε _ → center

module Exercise17
  {i} {A : 𝒰 i}
  {j} {B : ∥ A ∥ → Prop𝒰 j}
  where
  ∥-ind : ((a : A) → B ∣ a ∣ ty) → (x : ∥ A ∥) → B x ty
  ∥-ind f x = ∥-rec (transport (_ty ∘ B) center ∘ f) x
    where instance _ = λ {x} → hlevel𝒰.h (B x)

module Exercise18 {i} where
  open Exercise6

  _ : LEM {i} → LDN {i}
  _ = λ lem P f → +-rec id (𝟎-rec ∘ f) (lem P)

  _ : LDN {i} → LEM {i}
  _ = λ ldn P → ldn (type (P ty + ¬ P ty)) λ f → f (inr (f ∘ inl))

module Exercise19
  {i} {P : ℕ → 𝒰 i}
  (P-lem : (n : ℕ) → P n + ¬ P n)
  -- Do not assume that all P n are mere propositions so we can
  -- reuse this solution for exercise 23.
  where
  open import HoTT.NaturalNumber renaming (_+_ to _+ₙ_ ; +-comm to +ₙ-comm)
  open import HoTT.Identity.NaturalNumber
  open import HoTT.Transport.Identity
  open import HoTT.Base.Inspect
  open import HoTT.Identity.Product
  open import HoTT.Equivalence.Sigma
  open import HoTT.Equivalence.Coproduct
  open import HoTT.Equivalence.Empty

  -- P n does not hold for any m < n
  ℕ* : ℕ → 𝒰 i
  ℕ* zero = 𝟏
  ℕ* (succ n) = ¬ P n × ℕ* n

  P* : {n : ℕ} → P n → 𝒰 i
  P* {n} p = inl p == P-lem n

  -- ℕ* is the product of 𝟏 and some ¬ P n, all of which are
  -- propositions, so it is a proposition as well.
  instance ℕ*-hlevel : {n : ℕ} → hlevel 1 (ℕ* n)
  ℕ*-hlevel {zero} = 𝟏-hlevel
  ℕ*-hlevel {succ n} = ×-hlevel

  P*-hlevel : {n : ℕ} → hlevel 1 (Σ (P n) P*)
  hlevel-out (P*-hlevel {n}) {p , _} = ⟨⟩
    where
    e : P n ≃ P n + ¬ P n
    e = +-empty₂ ⁻¹ₑ ∙ₑ +-equiv reflₑ (𝟎-equiv (_$ p))
    instance
      _ = =-contrᵣ (P-lem n)
      _ = raise ⦃ equiv-hlevel (Σ-equiv₁ e ⁻¹ₑ) ⦄
  instance _ = P*-hlevel

  -- Extract evidence that ¬ P m for some m < n
  extract : {m n : ℕ} → m < n → ℕ* n → ¬ P m
  extract {m} (k , p) = pr₁ ∘ weaken ∘ transport ℕ* p'
    where
    p' = p ⁻¹ ∙ +ₙ-comm (succ m) k
    weaken : {k : ℕ} → ℕ* (k +ₙ succ m) → ℕ* (succ m)
    weaken {zero} = id
    weaken {succ k} = weaken ∘ pr₂

  -- The smallest n such that P n holds
  Pₒ = Σ (Σ ℕ λ n → Σ (P n) P*) (ℕ* ∘ pr₁)

  Pₒ-prop : isProp Pₒ
  Pₒ-prop ((n , p , _) , n*) ((m , q , _) , m*) =
    pair⁼ (pair⁼ (n=m , center) , center)
    where
    n=m : n == m
    n=m with n <=> m
    -- If n = m, then there is nothing to do.
    ... | inl n=m = n=m
    -- If n < m, we have P n and we know ℕ* m contains ¬ P n
    -- somewhere inside, so we can just extract it to find a
    -- contradiction.
    ... | inr (inl n<m) = 𝟎-rec (extract n<m m* p)
    -- The m < n case is symmetrical.
    ... | inr (inr m<n) = 𝟎-rec (extract m<n n* q)
  instance _ = isProp→hlevel1 Pₒ-prop

  -- Use the decidability of P to search for an instance of P in
  -- some finite range of natural numbers, keeping track of evidence
  -- that P does not hold for lower n.
  find-P : (n : ℕ) → Pₒ + ℕ* n
  find-P zero = inr ★
  find-P (succ n) with find-P n | P-lem n | inspect P-lem n
  ... | inl x  | _      | _      = inl x
  ... | inr n* | inl p  | [ p* ] = inl ((n , p , p*) , n*)
  ... | inr n* | inr ¬p | _      = inr (¬p , n*)

  -- If we know P holds for some n, then we have an upper bound for
  -- which to search for the smallest n. If we do not find any other
  -- n' ≤ n such that P n', then we have a contradiction.
  to-Pₒ : Σ ℕ P → Pₒ
  to-Pₒ (n , p) with find-P (succ n)
  ... | inl x = x
  ... | inr (¬p , _) = 𝟎-rec (¬p p)

  from-Pₒ : Pₒ → Σ ℕ P
  from-Pₒ ((n , p , p*) , n*) = n , p

  _ : ∥ Σ ℕ P ∥ → Σ ℕ P
  _ = from-Pₒ ∘ ∥-rec to-Pₒ

module Exercise20 where
  open variables

  -- See HoTT.HLevel
  _ : ⦃ _ : hlevel 0 A ⦄ → Σ A P ≃ P center
  _ = Σ-contr₁

module Exercise21 {i} {P : 𝒰 i} where
  open import HoTT.Equivalence.Proposition
  _ : isProp P ≃ (P ≃ ∥ P ∥)
  _ = prop-equiv ⦃ isProp-hlevel1 ⦄ f g
    where
    f : isProp P → P ≃ ∥ P ∥
    f p = prop-equiv ∣_∣ (∥-rec id)
      where instance _ = isProp→hlevel1 p
    g : P ≃ ∥ P ∥ → isProp P
    g e = hlevel1→isProp ⦃ equiv-hlevel (e ⁻¹ₑ) ⦄
    instance
      _ = Σ-hlevel ⦃ Π-hlevel ⦄ ⦃ isProp→hlevel1 isequiv-prop ⦄

module Exercise22 where
  Fin : ℕ → 𝒰₀
  Fin zero = 𝟎
  Fin (succ n) = Fin n + 𝟏

  □ : ∀ {i} (n : ℕ) {A : Fin n → 𝒰 i} {P : (x : Fin n) → A x → 𝒰 i} →
      ((x : Fin n) → ∥ Σ (A x) (P x) ∥) →
      ∥ Σ ((x : Fin n) → A x) (λ g → ((x : Fin n) → P x (g x))) ∥
  □ zero _ = ∣ 𝟎-ind , 𝟎-ind ∣
  □ (succ n) {A} {P} f =
    swap ∥-rec (f (inr ★))     λ zₛ →
    swap ∥-rec (□ n (f ∘ inl)) λ zₙ →
    let f = f' zₛ zₙ in ∣ pr₁ ∘ f , pr₂ ∘ f ∣
    where
    f' : _ → _ → (x : Fin (succ n)) → Σ (A x) (P x)
    f' (_ , _) (g , h) (inl m) = g m , h m
    f' (x , y) (_ , _) (inr ★) = x , y

module Exercise23 where
  -- The solution for Exercise19 covers the case where P is not
  -- necessarily a mere proposition.
  open Exercise19
