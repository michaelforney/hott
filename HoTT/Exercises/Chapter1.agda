module HoTT.Exercises.Chapter1 where

open import HoTT.Types hiding (_+_ ; inl ; inr)
open import HoTT.Identity hiding (=-ind')

module Exercise1 where
  _∘'_ : ∀ {i} {A B C : 𝒰 i} (g : B → C) (f : A → B) → A → C
  g ∘' f = λ x → g (f x)

  _ : ∀ {i} {A B C D : 𝒰 i} {f : A → B} {g : B → C} {h : C → D} →
      h ∘' (g ∘' f) == (h ∘' g) ∘' f
  _ = refl

module Exercise2 where
  ×-rec : ∀ {i} {A B : 𝒰 i}
           (C : 𝒰 i) → (A → B → C) → A × B → C
  ×-rec _ g x = g (pr₁ x) (pr₂ x)

  _ : ∀ {i} {A B C : 𝒰 i} {g : A → B → C} {a : A} {b : B} →
      ×-rec C g (a , b) == g a b
  _ = refl

  Σ-rec : ∀ {i} {A : 𝒰 i} {B : A → 𝒰 i}
           (C : 𝒰 i) → ((x : A) → B x → C) → Σ A B → C
  Σ-rec _ g x = g (pr₁ x) (pr₂ x)

  _ : ∀ {i} {A C : 𝒰 i} {B : A → 𝒰 i} {g : (x : A) → B x → C} {a : A} {b : B a} →
      Σ-rec C g (a , b) == g a b
  _ = refl

module Exercise3 where
  open import HoTT.Product using (×-uniq)
  open import HoTT.Sigma using (Σ-uniq)

  ×-ind : ∀ {i} {A B : 𝒰 i}
           (C : A × B → 𝒰 i) → ((a : A) → (b : B) → C (a , b)) → (x : A × B) → C x
  ×-ind C g x = transport {P = C} (×-uniq x) (g (pr₁ x) (pr₂ x))

  Σ-ind : ∀ {i} {A : 𝒰 i} {B : A → 𝒰 i}
          (C : Σ A B → 𝒰 i) → ((a : A) → (b : B a) → C (a , b)) → (x : Σ A B) → C x
  Σ-ind C g x = transport {P = C} (Σ-uniq x) (g (pr₁ x) (pr₂ x))

module Exerecise4 where
  iter : ∀ {i} (C : 𝒰 i) → C → (C → C) → ℕ → C
  iter C c₀ cₛ 0 = c₀
  iter C c₀ cₛ (succ n) = cₛ (iter C c₀ cₛ n)

  ℕ-rec : ∀ {i} (C : 𝒰 i) → C → (ℕ → C → C) → ℕ → C
  ℕ-rec C c₀ cₛ n = pr₂ (iter (ℕ × C) (0 , c₀) (λ{(n , c) → succ n , cₛ n c}) n)

  module _ {i} {C : 𝒰 i} {c₀ : C} {cₛ : ℕ → C → C} where
    eqn₁ : ℕ-rec C c₀ cₛ 0 == c₀
    eqn₁ = refl

    eqn₂ : {n : ℕ} → ℕ-rec C c₀ cₛ (succ n) == cₛ n (ℕ-rec C c₀ cₛ n)
    eqn₂ {n} = ap (λ m → cₛ m (ℕ-rec C c₀ cₛ n)) (lemma n)
      where
      lemma : (n : ℕ) → pr₁ (iter (ℕ × C) (0 , c₀) (λ{(n , c) → succ n , cₛ n c}) n) == n
      lemma 0 = refl
      lemma (succ n) = ap succ (lemma n)

module Exercise5 where
  open import HoTT.Boolean

  _+_ : ∀ {i j} → 𝒰 i → 𝒰 j → 𝒰 (i ⊔ j)
  _+_ {i} {j} A B = Σ 𝟐 λ x → 𝟐-rec (𝒰 _) (Lift {j} A) (Lift {i} B) x

  inl : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A → A + B
  inl a = 0₂ , lift a

  inr : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → B → A + B
  inr b = 1₂ , lift b

  +-ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
           (C : A + B → 𝒰 k) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
  +-ind C g₀ g₁ (0₂ , a) = g₀ (lower a)
  +-ind C g₀ g₁ (1₂ , b) = g₁ (lower b)

  prop₁ : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : A + B → 𝒰 k}
           {g₀ : (a : A) → C (inl a)} {g₁ : (b : B) → C (inr b)} {a : A} →
         +-ind C g₀ g₁ (inl a) == g₀ a
  prop₁ = refl

  prop₂ : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : A + B → 𝒰 k}
           {g₀ : (a : A) → C (inl a)} {g₁ : (b : B) → C (inr b)} {b : B} →
         +-ind C g₀ g₁ (inr b) == g₁ b
  prop₂ = refl

module Exercise6 where
  open import HoTT.Boolean
  open import HoTT.Pi

  _×'_ : ∀ {i j} → 𝒰 i → 𝒰 j → 𝒰 (i ⊔ j)
  _×'_ {i} {j} A B = (x : 𝟐) → 𝟐-rec (𝒰 (i ⊔ j)) (Lift {j} A) (Lift {i} B) x

  _,'_ : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} →
         A → B → A ×' B
  _,'_ {A = A} {B} a b = 𝟐-ind (𝟐-rec _ (Lift A) (Lift B)) (lift a) (lift b)

  pr₁' : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A ×' B → A
  pr₁' x = lower (x 0₂)

  pr₂' : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A ×' B → B
  pr₂' x = lower (x 1₂)

  ×'-up : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} →
          (x : A ×' B) → pr₁' x ,' pr₂' x == x
  ×'-up x = funext λ b → 𝟐-ind (λ b → (pr₁' x ,' pr₂' x) b == x b) refl refl b

  ×'-ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
           (C : A ×' B → 𝒰 k) → ((a : A) (b : B) → C (a ,' b)) → (x : A ×' B) → C x
  ×'-ind C g x = transport {P = C} (×'-up x) (g (pr₁' x) (pr₂' x))

  prop : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j}
           {C : A ×' B → 𝒰 k} {g : (a : A) (b : B) → C (a ,' b)} {a : A} {b : B} →
         ×'-ind C g (a ,' b) == g a b
  prop {C = C} {g} {a} {b} = ap (λ p → transport {P = C} p (g a b))
    (ap funext (funext (𝟐-ind (λ _ → _ == _) refl refl)) ∙ Π-identity-η refl)

  {-
  Alternative solution from https://github.com/pcapriotti/hott-exercises/blob/master/chapter1/ex6.agda

  ×'-up-compute : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} →
                  (x : A ×' B) → pr₁' x ,' pr₂' x == x
  ×'-up-compute x = (×'-up (pr₁' x ,' pr₂' x)) ⁻¹ ∙ ×'-up x

  ×'-ind : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} →
           (C : A ×' B → 𝒰 k) → ((a : A) (b : B) → C (a ,' b)) → (x : A ×' B) → C x
  ×'-ind C g x = transport {P = C} (×'-up-compute x) (g (pr₁' x) (pr₂' x))

  prop : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j}
           {C : A ×' B → 𝒰 k} {g : (a : A) (b : B) → C (a ,' b)} {a : A} {b : B} →
         ×'-ind C g (a ,' b) == g a b
  prop {C = C} {g} {a} {b} = ap (λ p → transport {P = C} p (g a b)) (linv (×'-up (a ,' b)))
  -}

module Exercise7 where
  open import HoTT.Sigma

  -- TODO: Using Lemma 3.11.8 might simplify this.
  =-ind' : ∀ {i j} {A : 𝒰 i} →
           (a : A) → (C : (x : A) → a == x → 𝒰 j) → C a refl → (x : A) → (p : a == x) → C x p
  =-ind' {i} {j} {A} a C c x p = transport {P = λ{(x , p) → C x p}} (pair⁼ (p , =-ind D d a x p)) c
    where
    D : (x y : A) → x == y → 𝒰 i
    D x y p = transport p refl == p
    d : (x : A) → D x x refl
    d x = refl

module Exercise8 where
  open import HoTT.NaturalNumber renaming (add to _+_)

  _*_ : ℕ → ℕ → ℕ
  n * m = ℕ-rec ℕ 0 (λ _ x → m + x) n

  _^_ : ℕ → ℕ → ℕ
  n ^ m = ℕ-rec ℕ 1 (λ _ x → m * x) n

  +-assoc : {a b c : ℕ} → (a + b) + c == a + (b + c)
  +-assoc {a} {b} {c} = ℕ-ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D a = (a + b) + c == a + (b + c)
    d₀ : D 0
    d₀ = refl
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = ap succ p

  +-ru : {a : ℕ} → a + 0 == a
  +-ru {a} = ℕ-ind (λ a → a + 0 == a) refl (λ _ → ap succ) a

  +-lu : {a : ℕ} → 0 + a == a
  +-lu = refl

  +-commute : {a b : ℕ} → a + b == b + a
  +-commute {a} = ℕ-ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D a = {b : ℕ} → a + b == b + a
    d₀ : D 0
    d₀ = +-lu ∙ +-ru ⁻¹
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p {b} = ap succ p ∙ ℕ-ind E e₀ eₛ b
      where
      E : ℕ → 𝒰₀
      E b = (succ b) + n == b + (succ n)
      e₀ : E 0
      e₀ = refl
      eₛ : (m : ℕ) → E m → E (succ m)
      eₛ m q = ap succ q

  *-lu : {a : ℕ} → 1 * a == a
  *-lu {a} = +-ru

  *-ru : {a : ℕ} → a * 1 == a
  *-ru {a} = ℕ-ind (λ a → a * 1 == a) refl (λ _ → ap succ) a

  *-ldistrib : {a b c : ℕ} → a * (b + c) == (a * b) + (a * c)
  *-ldistrib {a} {b} {c} = ℕ-ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D a = a * (b + c) == (a * b) + (a * c)
    d₀ : D 0
    d₀ = refl
    dₛ : (a : ℕ) → D a → D (succ a)
    dₛ a p = ap (_+_ (b + c)) p ∙
             +-assoc {b} {c} {(a * b) + (a * c)} ∙
             ap (_+_ b) (+-assoc {c} {a * b} {a * c} ⁻¹ ∙
                         ap (λ x → x + (a * c)) (+-commute {c} {a * b}) ∙
                         +-assoc {a * b} {c} {a * c}) ∙
             +-assoc {b} {a * b} {c + (a * c)} ⁻¹

  *-lz : {a : ℕ} → 0 * a == 0
  *-lz = refl

  *-rz : {a : ℕ} → a * 0 == 0
  *-rz {a} = ℕ-ind (λ n → n * 0 == 0) refl (λ _ p → p) a

  *-commute : {a b : ℕ} → a * b == b * a
  *-commute {a} {b} = ℕ-ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D n = n * b == b * n
    d₀ : D 0
    d₀ = *-rz {b} ⁻¹
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = ap (_+_ b) p ∙ ap (λ x → x + (b * n)) (*-ru {b} ⁻¹) ∙ *-ldistrib {b} {1} {n} ⁻¹

  *-rdistrib : {a b c : ℕ} → (a + b) * c == (a * c) + (b * c)
  *-rdistrib {a} {b} {c} = *-commute {a + b} {c} ∙
                           *-ldistrib {c} {a} {b} ∙
                           ap (λ x → x + (c * b)) (*-commute {c} {a}) ∙
                           ap (λ x → (a * c) + x) (*-commute {c} {b})

  *-assoc : {a b c : ℕ} → (a * b) * c == a * (b * c)
  *-assoc {a} {b} {c} = ℕ-ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D n = (n * b) * c == n * (b * c)
    d₀ : D 0
    d₀ = refl
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = *-rdistrib {b} {n * b} {c} ∙ ap (λ x → (b * c) + x) p

module Exercise9 where
  open import HoTT.NaturalNumber

  data Fin : ℕ → 𝒰₀ where
    fzero : {n : ℕ} → Fin (succ n)
    fsucc : {n : ℕ} → Fin n → Fin (succ n)

  fmax : (n : ℕ) → Fin (succ n)
  fmax n = ℕ-ind (λ n → Fin (succ n)) fzero (λ _ → fsucc) n

module Exercise10 where
  open import HoTT.NaturalNumber

  ack : ℕ → ℕ → ℕ
  ack m n = ℕ-rec (ℕ → ℕ) succ cₛ m n
    where
    cₛ : ℕ → (ℕ → ℕ) → ℕ → ℕ
    cₛ m c n = c (ℕ-rec ℕ 1 (λ _ → c) n)

module Exercise11 where
  open import HoTT.Empty

  prop : ∀ {i} {A : 𝒰 i} → ¬ ¬ ¬ A → ¬ A
  prop f a = f λ g → g a

module Exercise12 {i j} {A : 𝒰 i} {B : 𝒰 j} where
  open import HoTT.Types
  open import HoTT.Empty

  prop₁ : A → B → A
  prop₁ a _ = a

  prop₂ : A → ¬ ¬ A
  prop₂ a f = f a

  prop₃ : ¬ A + ¬ B → ¬ (A × B)
  prop₃ (inl a) x = a (pr₁ x)
  prop₃ (inr b) x = b (pr₂ x)

module Exercise13 where
  open import HoTT.Types
  open import HoTT.Empty

  prop : ∀ {i} {P : 𝒰 i} → ¬ ¬ (P + ¬ P)
  prop f = f (inr (f ∘ inl))

module Exercise14 where
  -- For induction, we must have a function C : (s : A) → (t : A) → (q : s == t) → U.
  -- Since q : s == t, the equality type q == refl {s} does not make sense because
  -- we are trying to equate elements of two different types.

module Exercise15 where
  prop : ∀ {i j} {A : 𝒰 i} →
         (C : A → 𝒰 j) → (x y : A) → (p : x == y) → C x → C y
  prop {i} {j} {A} C x y p = =-ind D d x y p
    where
    D : (x y : A) → x == y → 𝒰 j
    D x y p = C x → C y
    d : (x : A) → D x x refl
    d _ = id

module Exercise16 where
  -- This is just a subset of Exercise8. See +-commute above.
