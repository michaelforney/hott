{-# OPTIONS --without-K #-}
module HoTT.Exercises.Chapter2 where

open import HoTT.Types
open import HoTT.Identity

module Exercise1 {i} {A : 𝒰 i} (x y z : A) (p : x == y) (q : y == z) where
  Lemma2/1/2 : 𝒰 i
  Lemma2/1/2 = {x y z : A} → x == y → y == z → x == z

  -- Induction over p
  _∙₁_ : Lemma2/1/2
  _∙₁_ {x} {y} {z} p q = =-ind D d x y p z q where
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → x == z
    d : (x : A) → D x x refl
    d x z q = q

  -- Induction over q
  _∙₂_ : Lemma2/1/2
  _∙₂_ {x} {y} {z} p q = =-ind D d y z q x p where
    D : (y z : A) → y == z → 𝒰 i
    D y z q = (x : A) → (p : x == y) → x == z
    d : (y : A) → D y y refl
    d y x p = p

  -- Induction over p then q
  _∙₃_ : Lemma2/1/2
  _∙₃_ {x} {y} {z} p q = =-ind D d x y p z q where
    E : (x z : A) → (q : x == z) → 𝒰 i
    E x z q = x == z
    e : (x : A) → E x x refl
    e x = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → x == z
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

  prop₁₌₂ : p ∙₁ q == p ∙₂ q
  prop₁₌₂ = =-ind D d x y p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = refl ∙₁ q == refl ∙₂ q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₂ q
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

  prop₂₌₃ : p ∙₂ q == p ∙₃ q
  prop₂₌₃ = =-ind D d x y p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = refl ∙₂ q == refl ∙₃ q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → p ∙₂ q == p ∙₃ q
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

  prop₁₌₃ : p ∙₁ q == p ∙₃ q
  prop₁₌₃ = =-ind D d x y p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = refl ∙₁ q == refl ∙₃ q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₃ q
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

module Exercise2 {i} {A : 𝒰 i} {x y z : A} {p : x == y} {q : y == z} where
  open Exercise1 {i} {A} using (_∙₁_ ; _∙₂_ ; _∙₃_ ; prop₁₌₂ ; prop₂₌₃ ; prop₁₌₃)

  prop : prop₁₌₂ x y z p q ∙ prop₂₌₃ x y z p q == prop₁₌₃ x y z p q
  prop = =-ind D d x y p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = prop₁₌₂ y y z refl q ∙ prop₂₌₃ y y z refl q == prop₁₌₃ y y z refl q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → prop₁₌₂ x y z p q ∙ prop₂₌₃ x y z p q == prop₁₌₃ x y z p q
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

module Exercise3 {i} {A : 𝒰 i} (x y z : A) (p : x == y) (q : y == z) where
  open Exercise1 {i} {A} x y z p q using (Lemma2/1/2 ; _∙₁_)

  -- Induction over q then p
  _∙₄_ : Lemma2/1/2
  _∙₄_ {x} {y} {z} p q = =-ind D d y z q x p where
    E : (x y : A) → (p : x == y) → 𝒰 i
    E x y _ = x == y
    e : (x : A) → E x x refl
    e x = refl
    D : (y z : A) → y == z → 𝒰 i
    D y z q = (x : A) → (p : x == y) → x == z
    d : (y : A) → D y y refl
    d y x p = =-ind E e x y p

  prop₁₌₄ : p ∙₁ q == p ∙₄ q
  prop₁₌₄ = =-ind D d x y p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = refl ∙₁ q == refl ∙₄ q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₄ q
    d : (x : A) → D x x refl
    d x z q = =-ind E e x z q

module Exercise4 {i} {A : 𝒰 i} where
  open import HoTT.NaturalNumber

  n-path : ℕ → 𝒰 i
  n-path = ℕ-rec (𝒰 i) A (λ n c → Σ c (λ x → Σ c (λ y → x == y)))

module Exercise5 {i j} {A : 𝒰 i} {B : 𝒰 j} {x y : A} {p : x == y} {f : A → B} where
  open import HoTT.Equivalence

  prop : f x == f y ≃ transport p (f x) == f y
  prop = g , qinv→isequiv (h , α , β) where
    -- 2.3.6
    g : f x == f y → transport p (f x) == f y
    g = transportconst p (f x) ∙_
    -- 2.3.7
    h : transport p (f x) == f y → f x == f y
    h = transportconst p (f x) ⁻¹ ∙_
    α : (g ∘ h) ~ id
    α q = assoc (transportconst p (f x)) (transportconst p (f x) ⁻¹) q ∙
          ap (_∙ q) (=-rinv (transportconst p (f x))) ∙ lu q ⁻¹
    β : (h ∘ g) ~ id
    β q = assoc (transportconst p (f x) ⁻¹) (transportconst p (f x))q ∙
          ap (_∙ q) (=-linv (transportconst p (f x))) ∙ lu q ⁻¹

module Exercise6 {i} {A : 𝒰 i} {x y z : A} {p : x == y} where
  open import HoTT.Equivalence

  prop : y == z ≃ x == z
  prop = (p ∙_) , qinv→isequiv (p ⁻¹ ∙_ ,
     (λ q → assoc p (p ⁻¹) q ∙ ap (_∙ q) (=-rinv p) ∙ lu q ⁻¹) ,
     (λ q → assoc (p ⁻¹) p q ∙ ap (_∙ q) (=-linv p) ∙ lu q ⁻¹))

module Exercise7 {i j k l} {A : 𝒰 i} {A' : 𝒰 j} {B : A → 𝒰 k} {B' : A' → 𝒰 l}
                 {g : A → A'} {h : (x : A) → B x → B' (g x)} where
  open import HoTT.Sigma.Identity

  Lemma2/3/10 : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {P : B → 𝒰 k} {f : A → B} {x y : A} (p : x == y) (u : P (f x)) →
                transport {P = P ∘ f} p u == transport {P = P} (ap f p) u
  Lemma2/3/10 {P = P} {f} {x} {y} = =-ind
    (λ x y p → (u : P (f x)) → transport {P = P ∘ f} p u == transport {P = P} (ap f p) u)
    (λ _ _ → refl) x y

  Lemma2/3/11 : ∀ {i j k} {A : 𝒰 i} {P : A → 𝒰 j} {Q : A → 𝒰 k} {f : (x : A) → P x → Q x} {x y : A} (p : x == y) (u : P x) →
                transport {P = Q} p (f x u) == f y (transport {P = P} p u)
  Lemma2/3/11 {P = P} {Q} {f} {x} {y} = =-ind
    (λ x y p → (u : P x) → transport {P = Q} p (f x u) == f y (transport {P = P} p u))
    (λ _ _ → refl) x y

  f : Σ A B → Σ A' B'
  f x = g (pr₁ x) , h (pr₁ x) (pr₂ x)

  prop : {x y : Σ A B} {p : pr₁ x == pr₁ y} {q : transport p (pr₂ x) == pr₂ y} →
         ap f (pair⁼ (p , q)) == pair⁼
           (ap g p ,
            Lemma2/3/10 p (h (pr₁ x) (pr₂ x)) ⁻¹ ∙ Lemma2/3/11 {f = h} p (pr₂ x) ∙ ap (h (pr₁ y)) q)
  prop {x = x₁ , x₂} {y = y₁ , y₂} {p} {q} = =-ind D d x₁ y₁ p x₂ y₂ q where
    E : {x₁ : A} (x₂ y₂ : B x₁) → x₂ == y₂ → 𝒰 (j ⊔ l)
    E {x₁} x₂ y₂ q = ap f (pair⁼ (refl , q)) == pair⁼ (refl , refl ∙ refl ∙ ap (h x₁) q)
    e : {x₁ : A} (x₂ : B x₁) → E x₂ x₂ refl
    e _ = refl
    D : (x₁ y₁ : A) → x₁ == y₁ → 𝒰 (j ⊔ k ⊔ l)
    D x₁ y₁ p = (x₂ : B x₁) (y₂ : B y₁) (q : transport p x₂ == y₂) → ap f (pair⁼ (p , q)) == pair⁼
      (ap g p , Lemma2/3/10 p (h x₁ x₂) ⁻¹ ∙ Lemma2/3/11 {f = h} p x₂ ∙ ap (h y₁) q)
    d : (x₁ : A) → D x₁ x₁ refl
    d x₁ x₂ y₂ q = =-ind E e x₂ y₂ q

module Exercise8 {i j k l} {A : 𝒰 i} {B : 𝒰 j} {A' : 𝒰 k} {B' : 𝒰 l}
                 {g : A → A'} {h : B → B'} where
  open import HoTT.Coproduct

  f : A + B → A' + B'
  f = +-rec (A' + B') (inl ∘ g) (inr ∘ h)

  prop : {x y : A + B} {p : code x y} →
         ap f (decode p) == decode (+-ind (λ x → (y : A + B) → code x y → code (f x) (f y))
           (λ a y p → +-ind (λ y → code (inl a) y → code (f (inl a)) (f y))
             (λ a' (lift p) → lift (ap g p)) (λ b' (lift p) → (lift p)) y p)
           (λ b y p → +-ind (λ y → code (inr b) y → code (f (inr b)) (f y))
             (λ a' (lift p) → lift p) (λ b' (lift p) → lift (ap h p)) y p)
           x y p)
  prop {inl a} {inl .a} {lift refl} = refl
  prop {inl _} {inr _} {lift ()}
  prop {inr _} {inl _} {lift ()}
  prop {inr b} {inr .b} {lift refl} = refl

module Exercise9 {i j} {A : 𝒰 i} {B : 𝒰 j} where
  open import HoTT.Equivalence
  open import HoTT.Pi.Identity

  prop₁ : ∀ {k} {X : 𝒰 k} → (A + B → X) ≃ (A → X) × (B → X)
  prop₁ {X = X} = f , qinv→isequiv (g , α , β)
    where
    f : (A + B → X) → (A → X) × (B → X)
    f h = h ∘ inl , h ∘ inr
    g : (A → X) × (B → X) → (A + B → X)
    g (h , _) (inl a) = h a
    g (_ , h) (inr b) = h b
    α : f ∘ g ~ id
    α _ = refl
    β : g ∘ f ~ id
    β h = funext λ{(inl _) → refl ; (inr _) → refl}

  prop₂ : ∀ {k} {P : A + B → 𝒰 k} →
          ((x : A + B) → P x) ≃ ((a : A) → P (inl a)) × ((b : B) → P (inr b))
  prop₂ {P = P} = f , qinv→isequiv (g , α , β)
    where
    f : ((x : A + B) → P x) → ((a : A) → P (inl a)) × ((b : B) → P (inr b))
    f h = (h ∘ inl) , h ∘ inr
    g : ((a : A) → P (inl a)) × ((b : B) → P (inr b)) → ((x : A + B) → P x)
    g (h , _) (inl a) = h a
    g (_ , h) (inr b) = h b
    α : f ∘ g ~ id
    α _ = refl
    β : g ∘ f ~ id
    β h = funext λ{(inl _) → refl ; (inr _) → refl}

module Exercise10 {i j k} {A : 𝒰 i} {B : A → 𝒰 j} {C : Σ A B → 𝒰 k}
  where
  open import HoTT.Equivalence

  _ : (Σ A λ x → Σ (B x) λ y → C (x , y)) ≃ (Σ (Σ A B) λ p → C p)
  _ = f , qinv→isequiv (g , (λ _ → refl) , (λ _ → refl))
    where
    f : (Σ A λ x → Σ (B x) λ y → C (x , y)) → (Σ (Σ A B) λ p → C p)
    f (x , y , z) = (x , y) , z
    g : (Σ (Σ A B) λ p → C p) → (Σ A λ x → Σ (B x) λ y → C (x , y))
    g ((x , y) , z) = x , y , z

module Exercise11 {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} {f : A → C} {g : B → C}
  where
  open import HoTT.Equivalence
  open import HoTT.Pi.Identity
  open import HoTT.Sigma.Identity

  pullback : ∀ {i j k} (A : 𝒰 i) (B : 𝒰 j) {C : 𝒰 k} {f : A → C} {g : B → C} → 𝒰 _
  pullback A B {f = f} {g} = Σ A λ a → Σ B λ b → f a == g b

  P : 𝒰 (i ⊔ j ⊔ k)
  P = pullback A B {C} {f} {g}

  prop : ∀ {l} {X : 𝒰 l} → (X → P) ≃ pullback (X → A) (X → B)
  prop {X = X} = to , qinv→isequiv (from , α , β)
    where
    to : (X → P) → pullback (X → A) (X → B)
    to s = pr₁ ∘ s , pr₁ ∘ pr₂ ∘ s , funext (pr₂ ∘ pr₂ ∘ s)
    from : pullback (X → A) (X → B) → (X → P)
    from (h' , k' , p) x = h' x , k' x , happly p x
    α : to ∘ from ~ id
    α (_ , _ , p) = pair⁼ (refl , pair⁼ (refl , Π-identity-η p))
    β : from ∘ to ~ id
    β s = funext λ x → pair⁼ (refl , pair⁼ (refl , happly (Π-identity-β (pr₂ ∘ pr₂ ∘ s)) x))

module Exercise13
  where
  open import HoTT.Boolean
  open import HoTT.Equivalence
  open import HoTT.Pi.Identity
  open import HoTT.Sigma.Identity
  open import HoTT.Equivalence.Proposition

  not : 𝟐 → 𝟐
  not = 𝟐-rec 𝟐 1₂ 0₂

  -- There are two possibilities for 𝟐 ≃ 𝟐, id and not. In our
  -- equivalence (𝟐 ≃ 𝟐) ≃ 𝟐, we associate `id` with 0₂, and `not`
  -- with 1₂. For some f : 𝟐 ≃ 𝟐, we have f 0₂ = 0₂ when f is id,
  -- and f 0₂ = 1₂ when f is not, so we can use f 0₂ in the forward
  -- direction.
  _ : (𝟐 ≃ 𝟐) ≃ 𝟐
  _ = to , qinv→isequiv (from , α , β)
    where
    to : 𝟐 ≃ 𝟐 → 𝟐
    to e = (pr₁ e) 0₂
    from : 𝟐 → 𝟐 ≃ 𝟐
    from = 𝟐-rec _
      (id , qinv→isequiv (id , (λ _ → refl) , λ _ → refl))
      (not , qinv→isequiv (not , 𝟐-ind _ refl refl , 𝟐-ind _ refl refl))
    -- The first homotopy is easy, we just do 𝟐-induction on the
    -- input to determine whether we have `id` or `not`. Once we
    -- know that, it is just a matter of showing 0₂ = 0₂ or 1₂ = 1₂,
    -- both of which are true by reflection.
    α : to ∘ from ~ id
    α = 𝟐-ind _ refl refl
    -- The second homotopy is much trickier since we have to show
    -- that these two complex structures are the same. The approach
    -- we use is to induct on the four possibilities for f 0₂ and
    -- f 1₂ (0₂ 0₂, 0₂ 1₂, 1₂ 0₂, or 1₂ 1₂). In the induction goals,
    -- we require proofs that the boolean we induct on is equal
    -- to f 0₂ or f 1₂ respectively. These proofs can be used
    -- directly for the case where f = id or f = not. The other two
    -- cases are impossible unless 0₂ = 1₂, and we can use the
    -- proofs together with the equivalence inverse function and
    -- homotopy to show the desired behavior of f.
    β : from ∘ to ~ id
    β e = let f = pr₁ e
              h = pr₁ (pr₂ (pr₂ e))
              H = pr₂ (pr₂ (pr₂ e)) in
      pair⁼ (𝟐-ind (λ x → x == f 0₂ → pr₁ (from x) == f)
        (λ p → 𝟐-ind (λ x → x == f 1₂ → id == f)
          (λ q → funext (𝟐-ind _ p (H 1₂ ⁻¹ ∙ ap h (q ⁻¹ ∙ p) ∙ H 0₂ ∙ q)))
          (λ q → funext (𝟐-ind _ p q))
          (f 1₂) refl)
        (λ p → 𝟐-ind (λ x → x == f 1₂ → not == f)
          (λ q → funext (𝟐-ind _ p q))
          (λ q → funext (𝟐-ind _ p (H 0₂ ⁻¹ ∙ ap h (p ⁻¹ ∙ q) ∙ H 1₂ ∙ q)))
          (f 1₂) refl)
        (f 0₂) refl , isequiv-isProp _ _)

module Exercise14 {i} {A : 𝒰 i} {x : A}
  where
  -- In chapter 1 exercise 14, we showed that we couldn't use path
  -- induction to prove (x : A) → (p : x = x) → p = reflₓ since,
  -- given q : x = y, q = reflₓ is not well-typed (reflₓ : x = x,
  -- while q : x = y). However, using the equality reflection rule
  -- we have x ≡ y, so we can say reflₓ : x = y. Therefore, we can
  -- define
  --
  --   C : (x s : A) → x = y → 𝒰
  --   C x y q :≡ q = reflₓ
  --
  --   c : (x : A) → C x x reflₓ
  --   c x :≡ refl {reflₓ}
  --
  -- Using path induction we have ind₌ C c x x p : p = reflₓ. By
  -- applying the equality reflection rule again, we arrive at the
  -- desired definitional equality, p ≡ reflₓ.

module Exercise15 {i} {A : 𝒰 i} {B : A → 𝒰 i} {x y : A} {p : x == y} {u : B x}
  where
  open import HoTT.Universe.Identity

  _ : transport p == pr₁ (idtoeqv (ap B p))
  _ = =-ind (λ _ _ p → transport p == pr₁ (idtoeqv (ap B p)))
    (λ _ → refl) _ _ p

module Exercise16
  where
  open import HoTT.Equivalence
  open import HoTT.Pi.Identity using (funext ; happly)

  _ : ∀ {i} {A : 𝒰 i} {B : A → 𝒰 i} {f g : Π A B} →
      isequiv (happly {f = f} {g})
  _ = qinv→isequiv (funext , α , β)
    where
    -- "may require concepts from later chapters"
    postulate
      α : happly ∘ funext ~ id
      β : funext ∘ happly ~ id

module Exercise17 {i}
  where
  open import HoTT.Equivalence
  open import HoTT.Product.Identity
  open import HoTT.Universe.Identity
  open import HoTT.Pi.Identity

  variable
    A A' B B' : 𝒰 i
    P : A → 𝒰 i
    P' : A' → 𝒰 i

  module _ (e₁ : A ≃ A') (e₂ : B ≃ B')
    where
    -- (i) Proof without using univalence
    prop-×' : (A × B) ≃ (A' × B')
    prop-×' =
      let f₁ = pr₁ e₁ ; f₂ = pr₁ e₂
          (g₁ , α₁ , β₁) = isequiv→qinv (pr₂ e₁)
          (g₂ , α₂ , β₂) = isequiv→qinv (pr₂ e₂)
      in (λ (a , b) → f₁ a , f₂ b) , qinv→isequiv
        ( (λ (a' , b') → g₁ a' , g₂ b')
        , (λ (a' , b') → pair⁼ (α₁ a' , α₂ b'))
        , (λ (a , b) → pair⁼ (β₁ a , β₂ b)) )

    -- (ii) Proof using univalence (for general operator)
    prop : (_⊙_ : 𝒰 i → 𝒰 i → 𝒰 i) → (A ⊙ B) ≃ (A' ⊙ B')
    prop (_⊙_) = =-ind' A (λ A' _ → (A ⊙ B) ≃ (A' ⊙ B'))
      (=-ind' B (λ B' _ → (A ⊙ B) ≃ (A ⊙ B')) (idtoeqv refl) B' (ua e₂))
      A' (ua e₁)

    prop-× = prop _×_

    -- TODO: Proofs of (i) and (ii) are equal
    postulate
      _ : prop-×' == prop-×

    -- (iii) Proof for non-dependent type formers (→, +)
    prop-→ = prop (λ A B → A → B)
    prop-+ = prop _+_

  module _ (e₁ : A ≃ A') (e₂ : transport {P = λ A' → A' → 𝒰 i} (ua e₁) P ~ P')
    where
    prop-dep : (_⊙_ : (A : 𝒰 i) → (A → 𝒰 i) → 𝒰 i) → (A ⊙ P) ≃ (A' ⊙ P')
    prop-dep _⊙_ = =-ind' A
      (λ A' p → (P' : A' → 𝒰 i) → transport p P ~ P' → (A ⊙ P) ≃ (A' ⊙ P'))
      (λ P' q → =-ind' P (λ P' _ → A ⊙ P ≃ A ⊙ P') (idtoeqv refl) P' (funext q))
      A' (ua e₁) P' e₂

    -- (iii) Proof for dependent type formers (Σ, Π)
    prop-Σ = prop-dep Σ
    prop-Π = prop-dep Π
