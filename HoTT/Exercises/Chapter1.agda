{-# OPTIONS --without-K #-}
open import HoTT.Base using (𝒰 ; Level ; module variables)

module HoTT.Exercises.Chapter1 where

open variables

module Exercise1 where
  open HoTT.Base hiding (_∘_)

  _∘_ : {A B C : 𝒰 i} (g : B → C) (f : A → B) → A → C
  g ∘ f = λ x → g (f x)

  _ : {A B C D : 𝒰 i} {f : A → B} {g : B → C} {h : C → D} →
      h ∘ (g ∘ f) == (h ∘ g) ∘ f
  _ = refl

module Exercise2 where
  open HoTT.Base hiding (×-rec ; Σ-rec)

  ×-rec : (C : 𝒰 i) → (A → B → C) → A × B → C
  ×-rec _ g x = g (pr₁ x) (pr₂ x)

  _ : {C : 𝒰 i} {g : A → B → C} {a : A} {b : B} →
      ×-rec C g (a , b) == g a b
  _ = refl

  Σ-rec : (C : 𝒰 i) → ((x : A) → P x → C) → Σ A P → C
  Σ-rec _ g x = g (pr₁ x) (pr₂ x)

  _ : {C : 𝒰 i} {g : (x : A) → P x → C} {a : A} {b : P a} →
      Σ-rec C g (a , b) == g a b
  _ = refl

module Exercise3 where
  open HoTT.Base hiding (×-ind ; Σ-ind)

  ×-ind : {A B : 𝒰 i} (C : A × B → 𝒰 i) →
            ((a : A) → (b : B) → C (a , b)) → (x : A × B) → C x
  ×-ind C g x = transport C (×-uniq x) (g (pr₁ x) (pr₂ x))

  Σ-ind : {A : 𝒰 i} {B : A → 𝒰 i} (C : Σ A B → 𝒰 i) →
          ((a : A) → (b : B a) → C (a , b)) → (x : Σ A B) → C x
  Σ-ind C g x = transport C (Σ-uniq x) (g (pr₁ x) (pr₂ x))

module Exercise4 where
  open HoTT.Base hiding (ℕ-rec)

  iter : (C : 𝒰 i) → C → (C → C) → ℕ → C
  iter C c₀ cₛ 0 = c₀
  iter C c₀ cₛ (succ n) = cₛ (iter C c₀ cₛ n)

  f : {C : 𝒰 i} {cₛ : ℕ → C → C} → ℕ × C → ℕ × C
  f {cₛ = cₛ} (n , c) = succ n , cₛ n c

  iterℕ : (C : 𝒰 i) → C → (ℕ → C → C) → ℕ → ℕ × C
  iterℕ C c₀ cₛ n = iter (ℕ × C) (0 , c₀) (f {C = C} {cₛ = cₛ}) n

  ℕ-rec : (C : 𝒰 i) → C → (ℕ → C → C) → ℕ → C
  ℕ-rec C c₀ cₛ n = pr₂ (iterℕ C c₀ cₛ n)

  module _ {C : 𝒰 i} {c₀ : C} {cₛ : ℕ → C → C} where
    _ : ℕ-rec C c₀ cₛ 0 == c₀
    _ = refl

    _ : (n : ℕ) → ℕ-rec C c₀ cₛ (succ n) == cₛ n (ℕ-rec C c₀ cₛ n)
    _ = ℕ-ind D d₀ dₛ
      where
      E : ℕ → 𝒰₀
      E n = pr₁ (iterℕ C c₀ cₛ n) == n
      e₀ : E 0
      e₀ = refl
      eₛ : (n : ℕ) → E n → E (succ n)
      eₛ n = ×-ind (λ z → pr₁ z == n → pr₁ (f z) == succ n)
        (λ _ _ p → ap succ p) (iterℕ C c₀ cₛ n)

      D : ℕ → 𝒰 i
      D n = ℕ-rec C c₀ cₛ (succ n) == cₛ n (ℕ-rec C c₀ cₛ n)
      d₀ : D 0
      d₀ = refl
      dₛ : (n : ℕ) → D n → D (succ n)
      dₛ n _ = ×-ind (λ z → pr₁ z == n → pr₂ (f (f z)) == cₛ (succ n) (pr₂ (f z)))
        (λ x y p → ap (λ n → cₛ (succ n) (cₛ x y)) p)
        (iterℕ C c₀ cₛ n) (ℕ-ind E e₀ eₛ n)

module Exercise5 where
  open HoTT.Base hiding (_+_ ; inl ; inr ; +-ind)

  _+_ : 𝒰 i → 𝒰 i → 𝒰 i
  _+_ A B = Σ[ x ∶ 𝟐 ] (𝟐-rec A B x)

  private variable C : A + B → 𝒰 i

  inl : A → A + B
  inl a = 0₂ , a

  inr : B → A + B
  inr b = 1₂ , b

  +-ind : (C : A + B → 𝒰 i) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) →
          (x : A + B) → C x
  +-ind C g₀ g₁ (0₂ , a) = g₀ a
  +-ind C g₀ g₁ (1₂ , b) = g₁ b

  _ : {g₀ : (a : A) → C (inl a)} {g₁ : (b : B) → C (inr b)} {a : A} →
      +-ind C g₀ g₁ (inl a) == g₀ a
  _ = refl

  _ : {g₀ : (a : A) → C (inl a)} {g₁ : (b : B) → C (inr b)} {b : B} →
      +-ind C g₀ g₁ (inr b) == g₁ b
  _ = refl

module Exercise6 where
  open HoTT.Base hiding (_×_ ; _,_ ; pr₁ ; pr₂ ; ×-uniq ; ×-ind)
  open import HoTT.Identity.Pi

  _×_ : 𝒰 i → 𝒰 i → 𝒰 i
  _×_ A B = (x : 𝟐) → 𝟐-rec A B x

  _,_ : A → B → A × B
  _,_ a b = 𝟐-ind _ a b

  pr₁ : A × B → A
  pr₁ x = x 0₂

  pr₂ : A × B → B
  pr₂ x = x 1₂

  ×-uniq : (x : A × B) → pr₁ x , pr₂ x == x
  ×-uniq x = funext λ b → 𝟐-ind (λ b → (pr₁ x , pr₂ x) b == x b) refl refl b

  ×-ind : (C : A × B → 𝒰 i) → ((a : A) (b : B) → C (a , b)) → (x : A × B) → C x
  ×-ind C g x = transport C (×-uniq x) (g (pr₁ x) (pr₂ x))

  module _ {C : A × B → 𝒰 i} {g : (a : A) (b : B) → C (a , b)} {a : A} {b : B}
    where
    _ : ×-ind C g (a , b) == g a b
    _ = ap (λ p → transport C p (g a b))
          (ap funext (funext (𝟐-ind _ refl refl)) ∙ =Π-η refl)

  -- Alternative solution from https://pcapriotti.github.io/hott-exercises/chapter1.ex6.html
  {-
  ×-uniq-compute : (x : A × B) → pr₁ x , pr₂ x == x
  ×-uniq-compute x = ×-uniq (pr₁ x , pr₂ x) ⁻¹ ∙ ×-uniq x

  ×-ind' : (C : A × B → 𝒰 i) → ((a : A) (b : B) → C (a , b)) → (x : A × B) → C x
  ×-ind' C g x = transport C (×-uniq-compute x) (g (pr₁ x) (pr₂ x))

  module _ {C : A × B → 𝒰 i} {g : (a : A) (b : B) → C (a , b)} {a : A} {b : B}
    where
    _ : ×-ind' C g (a , b) == g a b
    _ = ap (λ p → transport C p (g a b)) (∙-invₗ (×-uniq (a , b)))
  -}


module Exercise7 where
  open HoTT.Base hiding (=-ind')
  open import HoTT.Identity.Sigma
  open import HoTT.Identity

  -- TODO: Using Lemma 3.11.8 might simplify this.
  =-ind' : (a : A) → (C : (x : A) → a == x → 𝒰 j) →
           C a refl → (x : A) → (p : a == x) → C x p
  =-ind' {A = A} a C c x p = transport (λ{(x , p) → C x p}) q c
    where
    D : (x y : A) → x == y → 𝒰 _
    D x y p = transport (x ==_) p refl == p
    d : (x : A) → D x x refl
    d x = refl

    q : (a , refl) == (x , p)
    q = pair⁼ (p , =-ind D d p)

module Exercise8 where
  open HoTT.Base hiding (_+_) renaming (ℕ-rec to rec ; ℕ-ind to ind)
  open import HoTT.Identity

  _+_ : ℕ → ℕ → ℕ
  n + m = rec m (λ _ → succ) n
  infix 17 _+_

  _*_ : ℕ → ℕ → ℕ
  n * m = rec 0 (λ _ x → m + x) n
  infix 18 _*_

  _^_ : ℕ → ℕ → ℕ
  n ^ m = rec 1 (λ _ x → m * x) n
  infix 19 _^_

  +-assoc : (a b c : ℕ) → (a + b) + c == a + (b + c)
  +-assoc a b c = ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D a = (a + b) + c == a + (b + c)
    d₀ : D 0
    d₀ = refl
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = ap succ p

  +-unitₗ : (a : ℕ) → 0 + a == a
  +-unitₗ a = refl

  +-unitᵣ : (a : ℕ) → a + 0 == a
  +-unitᵣ a = ind (λ a → a + 0 == a) refl (λ _ → ap succ) a

  +-commute : (a b : ℕ) → a + b == b + a
  +-commute = ind D d₀ dₛ
    where
    D : ℕ → 𝒰₀
    D a = (b : ℕ) → a + b == b + a
    d₀ : D 0
    d₀ b = +-unitₗ b ∙ +-unitᵣ b ⁻¹
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p b = ap succ (p b) ∙ ind E e₀ eₛ b
      where
      E : ℕ → 𝒰₀
      E b = (succ b) + n == b + (succ n)
      e₀ : E 0
      e₀ = refl
      eₛ : (m : ℕ) → E m → E (succ m)
      eₛ m q = ap succ q

  *-unitₗ : (a : ℕ) → 1 * a == a
  *-unitₗ = +-unitᵣ

  *-unitᵣ : (a : ℕ) → a * 1 == a
  *-unitᵣ = ind (λ a → a * 1 == a) refl (λ _ → ap succ)

  *-distₗ : (a b c : ℕ) → a * (b + c) == a * b + a * c
  *-distₗ a b c = ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D a = a * (b + c) == a * b + a * c
    d₀ : D 0
    d₀ = refl
    dₛ : (a : ℕ) → D a → D (succ a)
    dₛ a p =
      succ a * (b + c)          =⟨⟩
      (b + c) + a * (b + c)     =⟨ ap ((b + c) +_) p ⟩
      (b + c) + (a * b + a * c) =⟨ +-assoc b c (a * b + a * c) ⟩
      b + (c + (a * b + a * c)) =⟨ ap (b +_) (+-assoc c (a * b) (a * c) ⁻¹) ⟩
      b + ((c + a * b) + a * c) =⟨ ap (λ n → b + (n + a * c)) (+-commute c (a * b)) ⟩
      b + ((a * b + c) + a * c) =⟨ ap (b +_) (+-assoc (a * b) c (a * c)) ⟩
      b + (a * b + (c + a * c)) =⟨ +-assoc b (a * b) (c + a * c) ⁻¹ ⟩
      (b + a * b) + (c + a * c) =⟨⟩
      succ a * b + succ a * c   ∎
      where open =-Reasoning

  *-zeroₗ : (a : ℕ) → 0 * a == 0
  *-zeroₗ _ = refl

  *-zeroᵣ : (a : ℕ) → a * 0 == 0
  *-zeroᵣ a = ind (λ n → n * 0 == 0) refl (λ _ p → p) a

  *-comm : (a b : ℕ) → a * b == b * a
  *-comm a b = ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D n = n * b == b * n
    d₀ : D 0
    d₀ = *-zeroᵣ b ⁻¹
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = ap (b +_) p ∙ ap (_+ (b * n)) (*-unitᵣ b ⁻¹) ∙ *-distₗ b 1 n ⁻¹

  *-distᵣ : (a b c : ℕ) → (a + b) * c == (a * c) + (b * c)
  *-distᵣ a b c =
    (a + b) * c   =⟨ *-comm (a + b) c ⟩
    c * (a + b)   =⟨ *-distₗ c a b ⟩
    c * a + c * b =⟨ ap (_+ (c * b)) (*-comm c a) ⟩
    a * c + c * b =⟨ ap ((a * c) +_) (*-comm c b) ⟩
    a * c + b * c ∎
    where open =-Reasoning

  *-assoc : (a b c : ℕ) → (a * b) * c == a * (b * c)
  *-assoc a b c = ind D d₀ dₛ a
    where
    D : ℕ → 𝒰₀
    D n = (n * b) * c == n * (b * c)
    d₀ : D 0
    d₀ = refl
    dₛ : (n : ℕ) → D n → D (succ n)
    dₛ n p = *-distᵣ b (n * b) c ∙ ap ((b * c) +_) p

module Exercise9 where
  open HoTT.Base

  Fin : ℕ → 𝒰₀
  Fin n = ℕ-rec 𝟎 (λ _ A → 𝟏 + A) n

  fmax : (n : ℕ) → Fin (succ n)
  fmax = ℕ-ind (Fin ∘ succ) (inl ★) (λ _ → inr)

module Exercise10 where
  open HoTT.Base

  ack : ℕ → ℕ → ℕ
  ack m n = ℕ-rec succ cₛ m n
    where
    cₛ : ℕ → (ℕ → ℕ) → ℕ → ℕ
    cₛ m c n = c (ℕ-rec 1 (λ _ → c) n)

module Exercise11 where
  open HoTT.Base

  _ : ¬ ¬ ¬ A → ¬ A
  _ = λ f a → f (λ g → g a)

module Exercise12 where
  open HoTT.Base

  _ : A → B → A
  _ = λ a _ → a

  _ : A → ¬ ¬ A
  _ = λ a f → f a

  _ : ¬ A + ¬ B → ¬ (A × B)
  _ = λ x y → +-rec (λ f → 𝟎-rec (f (pr₁ y))) (λ f → 𝟎-rec (f (pr₂ y))) x

module Exercise13 where
  open HoTT.Base

  _ : ¬ ¬ (A + ¬ A)
  _ = λ f → f (inr (f ∘ inl))

module Exercise14 where
  -- For induction, we must have a function C : (s : A) → (t : A) → (q : s == t) → 𝒰.
  -- Since q : s == t, the equality type q == refl {s} does not make sense because
  -- we are trying to equate elements of two different types.

module Exercise15 {C : A → 𝒰 i} where
  open HoTT.Base using (_==_ ; refl ; =-ind ; id)

  _ : {x y : A} → (p : x == y) → C x → C y
  _ = =-ind D d
    where
    D : (x y : A) → x == y → 𝒰 _
    D x y p = C x → C y
    d : (x : A) → D x x refl
    d _ = id

module Exercise16 where
  -- This is just a subset of Exercise8. See +-commute above.
