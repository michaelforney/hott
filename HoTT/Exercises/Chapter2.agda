{-# OPTIONS --without-K #-}
module HoTT.Exercises.Chapter2 where

open import HoTT.Base

module Exercise1 {i} {A : 𝒰 i} where
  module _ {x y z : A} (p : x == y) (q : y == z) where
    -- Induction over p
    _∙₁_ : x == z
    _∙₁_ = =-ind D d p z q where
      D : (x y : A) → x == y → 𝒰 i
      D x y p = (z : A) → (q : y == z) → x == z
      d : (x : A) → D x x refl
      d x z q = q

    -- Induction over q
    _∙₂_ : x == z
    _∙₂_ = =-ind D d q x p where
      D : (y z : A) → y == z → 𝒰 i
      D y z q = (x : A) → (p : x == y) → x == z
      d : (y : A) → D y y refl
      d y x p = p

    -- Induction over p then q
    _∙₃_ : x == z
    _∙₃_ = =-ind D d p z q where
      E : (x z : A) → (q : x == z) → 𝒰 i
      E x z q = x == z
      e : (x : A) → E x x refl
      e x = refl
      D : (x y : A) → x == y → 𝒰 i
      D x y p = (z : A) → (q : y == z) → x == z
      d : (x : A) → D x x refl
      d x z q = =-ind E e q

  module _ {x y z : A} (p : x == y) (q : y == z) where
    prop₁₌₂ : p ∙₁ q == p ∙₂ q
    prop₁₌₂ = =-ind D d p z q where
      E : (y z : A) → y == z → 𝒰 i
      E y z q = refl ∙₁ q == refl ∙₂ q
      e : (y : A) → E y y refl
      e y = refl
      D : (x y : A) → x == y → 𝒰 i
      D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₂ q
      d : (x : A) → D x x refl
      d x z q = =-ind E e q

    prop₂₌₃ : p ∙₂ q == p ∙₃ q
    prop₂₌₃ = =-ind D d p z q where
      E : (y z : A) → y == z → 𝒰 i
      E y z q = refl ∙₂ q == refl ∙₃ q
      e : (y : A) → E y y refl
      e y = refl
      D : (x y : A) → x == y → 𝒰 i
      D x y p = (z : A) → (q : y == z) → p ∙₂ q == p ∙₃ q
      d : (x : A) → D x x refl
      d x z q = =-ind E e q

    prop₁₌₃ : p ∙₁ q == p ∙₃ q
    prop₁₌₃ = =-ind D d p z q where
      E : (y z : A) → y == z → 𝒰 i
      E y z q = refl ∙₁ q == refl ∙₃ q
      e : (y : A) → E y y refl
      e y = refl
      D : (x y : A) → x == y → 𝒰 i
      D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₃ q
      d : (x : A) → D x x refl
      d x z q = =-ind E e q

module Exercise2 {i} {A : 𝒰 i} {x y z : A} {p : x == y} {q : y == z} where
  open Exercise1

  _ : prop₁₌₂ p q ∙ prop₂₌₃ p q == prop₁₌₃ p q
  _ = =-ind D d p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = prop₁₌₂ refl q ∙ prop₂₌₃ refl q == prop₁₌₃ refl q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → prop₁₌₂ p q ∙ prop₂₌₃ p q == prop₁₌₃ p q
    d : (x : A) → D x x refl
    d x z q = =-ind E e q

module Exercise3 {i} {A : 𝒰 i} where
  open Exercise1 using (_∙₁_)

  -- Induction over q then p
  _∙₄_ : {x y z : A} → x == y → y == z → x == z
  _∙₄_ {x} {y} {z} p q = =-ind D d q x p where
    E : (x y : A) → (p : x == y) → 𝒰 i
    E x y _ = x == y
    e : (x : A) → E x x refl
    e x = refl
    D : (y z : A) → y == z → 𝒰 i
    D y z q = (x : A) → (p : x == y) → x == z
    d : (y : A) → D y y refl
    d y x p = =-ind E e p

  prop₁₌₄ : {x y z : A} (p : x == y) (q : y == z) → p ∙₁ q == p ∙₄ q
  prop₁₌₄ {x} {y} {z} p q = =-ind D d p z q where
    E : (y z : A) → y == z → 𝒰 i
    E y z q = refl ∙₁ q == refl ∙₄ q
    e : (y : A) → E y y refl
    e y = refl
    D : (x y : A) → x == y → 𝒰 i
    D x y p = (z : A) → (q : y == z) → p ∙₁ q == p ∙₄ q
    d : (x : A) → D x x refl
    d x z q = =-ind E e q

module Exercise4 {i} (A : 𝒰 i) where
  n-path : ℕ → 𝒰 i
  n-path = ℕ-rec A (λ n P → Σ[ x ∶ P ] (Σ[ y ∶ P ] (x == y)))

module Exercise5 {i} {A B : 𝒰 i} {x y : A} {p : x == y} {f : A → B} where
  open import HoTT.Identity
  open import HoTT.Equivalence

  _ : f x == f y ≃ transport _ p (f x) == f y
  _ = g , qinv→isequiv (h , η , ε)
    where
    -- 2.3.6
    g : f x == f y → transport _ p (f x) == f y
    g = transportconst p (f x) ∙_
    -- 2.3.7
    h : transport _ p (f x) == f y → f x == f y
    h = transportconst p (f x) ⁻¹ ∙_
    η : (h ∘ g) ~ id
    η q = assoc ∙ (invₗ ∙ᵣ q ∙ unitₗ ⁻¹)
    ε : (g ∘ h) ~ id
    ε q = assoc ∙ (invᵣ ∙ᵣ q ∙ unitₗ ⁻¹)


module Exercise6 {i} {A : 𝒰 i} {x y z : A} {p : x == y} where
  open import HoTT.Equivalence
  open import HoTT.Identity

  _ : y == z ≃ x == z
  _ = f , qinv→isequiv (g , η , ε)
    where
    f = p ∙_
    g = p ⁻¹ ∙_
    η : g ∘ f ~ id
    η q = assoc ∙ (invₗ ∙ᵣ q ∙ unitₗ ⁻¹)
    ε : f ∘ g ~ id
    ε q = assoc ∙ (invᵣ ∙ᵣ q ∙ unitₗ ⁻¹)

module Exercise7 {i j k l} {A : 𝒰 i} {A' : 𝒰 j} {B : A → 𝒰 k} {B' : A' → 𝒰 l}
                 {g : A → A'} {h : {x : A} → B x → B' (g x)} where
  open import HoTT.Identity
  open import HoTT.Identity.Sigma

  prop : {x y : Σ A B} (p : pr₁ x == pr₁ y) (q : transport B p (pr₂ x) == (pr₂ y)) →
         ap (λ x → g (pr₁ x) , h (pr₂ x)) (pair⁼ {x = x} {y} (p , q)) ==
         pair⁼ (ap g p , transport-ap B' g p (h (pr₂ x)) ∙ transport-∘ h p (pr₂ x) ∙ ap h q)
  prop {x = _ , _} {_ , _} refl refl = refl

module Exercise8 {i j k l} {A : 𝒰 i} {B : 𝒰 j} {A' : 𝒰 k} {B' : 𝒰 l}
                 {g : A → A'} {h : B → B'} where
  open import HoTT.Identity.Coproduct

  private variable x y : A + B

  f : A + B → A' + B'
  f = +-rec (inl ∘ g) (inr ∘ h)

  ap-gh : (p : x =+ y) → f x =+ f y
  ap-gh {inl _} {inl _} (lift p) = lift (ap g p)
  ap-gh {inl _} {inr _} ()
  ap-gh {inr _} {inl _} ()
  ap-gh {inr _} {inr _} (lift p) = lift (ap h p)

  prop : (p : x =+ y) → ap f (=+-intro p) == =+-intro (ap-gh p)
  prop {inl _} {inl _} (lift refl) = refl
  prop {inl _} {inr _} ()
  prop {inr _} {inl _} ()
  prop {inr _} {inr _} (lift refl) = refl

module Exercise9 {i j k} {A : 𝒰 i} {B : 𝒰 j} where
  open import HoTT.Equivalence
  open import HoTT.Identity.Pi

  prop₁ : {X : 𝒰 k} → (A + B → X) ≃ (A → X) × (B → X)
  prop₁ {X} = f , qinv→isequiv (g , β , α)
    where
    f : (A + B → X) → (A → X) × (B → X)
    f h = h ∘ inl , h ∘ inr
    g : (A → X) × (B → X) → (A + B → X)
    g (h , _) (inl a) = h a
    g (_ , h) (inr b) = h b
    α : f ∘ g ~ id
    α (_ , _) = refl
    β : g ∘ f ~ id
    β _ = funext λ{(inl _) → refl ; (inr _) → refl}

  prop₂ : {P : A + B → 𝒰 k} →
          ((x : A + B) → P x) ≃ ((a : A) → P (inl a)) × ((b : B) → P (inr b))
  prop₂ {P} = f , qinv→isequiv (g , β , α)
    where
    f : ((x : A + B) → P x) → ((a : A) → P (inl a)) × ((b : B) → P (inr b))
    f h = (h ∘ inl) , h ∘ inr
    g : ((a : A) → P (inl a)) × ((b : B) → P (inr b)) → ((x : A + B) → P x)
    g (h , _) (inl a) = h a
    g (_ , h) (inr b) = h b
    α : f ∘ g ~ id
    α (_ , _) = refl
    β : g ∘ f ~ id
    β _ = funext λ{(inl _) → refl ; (inr _) → refl}

module Exercise10 {i j k} {A : 𝒰 i} {B : A → 𝒰 j} {C : Σ A B → 𝒰 k}
  where
  open import HoTT.Equivalence

  _ : Σ[ x ∶ A ] Σ[ y ∶ B x ] C (x , y) ≃ Σ[ p ∶ Σ A B ] C p
  _ = f , qinv→isequiv (g , η , ε)
    where
    f : Σ[ x ∶ A ] Σ[ y ∶ B x ] C (x , y) → Σ[ p ∶ Σ A B ] C p
    f (x , y , z) = (x , y) , z
    g : Σ[ p ∶ Σ A B ] C p → Σ[ x ∶ A ] Σ[ y ∶ B x ] C (x , y)
    g ((x , y) , z) = x , y , z
    η : g ∘ f ~ id
    η (_ , _ , _) = refl
    ε : f ∘ g ~ id
    ε ((_ , _) , _) = refl

import HoTT.Exercises.Chapter2.Exercise11

import HoTT.Exercises.Chapter2.Exercise12

module Exercise13
  where
  open import HoTT.Equivalence
  open import HoTT.Equivalence.Proposition
  open import HoTT.Identity.Pi
  open import HoTT.Identity.Sigma

  not : 𝟐 → 𝟐
  not = 𝟐-rec 1₂ 0₂

  -- There are two possibilities for 𝟐 ≃ 𝟐, id and not. In our
  -- equivalence (𝟐 ≃ 𝟐) ≃ 𝟐, we associate `id` with 0₂, and `not`
  -- with 1₂. For some f : 𝟐 ≃ 𝟐, we have f 0₂ = 0₂ when f is id,
  -- and f 0₂ = 1₂ when f is not, so we can use f 0₂ in the forward
  -- direction.
  _ : (𝟐 ≃ 𝟐) ≃ 𝟐
  _ = to , qinv→isequiv (from , β , α)
    where
    to : 𝟐 ≃ 𝟐 → 𝟐
    to (f , _) = f 0₂
    from : 𝟐 → 𝟐 ≃ 𝟐
    from 0₂ = id , qinv→isequiv (id , (λ _ → refl) , λ _ → refl)
    from 1₂ = not , qinv→isequiv (not , 𝟐-ind _ refl refl , 𝟐-ind _ refl refl)
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
    β (f , e) =
      pair⁼ (𝟐-ind (λ x → x == f 0₂ → pr₁ (from x) == f)
        (λ p → 𝟐-ind (λ x → x == f 1₂ → id == f)
          (λ q → funext (𝟐-ind _ p (η 1₂ ⁻¹ ∙ ap g (q ⁻¹ ∙ p) ∙ η 0₂ ∙ q)))
          (λ q → funext (𝟐-ind _ p q))
          (f 1₂) refl)
        (λ p → 𝟐-ind (λ x → x == f 1₂ → not == f)
          (λ q → funext (𝟐-ind _ p q))
          (λ q → funext (𝟐-ind _ p (η 0₂ ⁻¹ ∙ ap g (p ⁻¹ ∙ q) ∙ η 1₂ ∙ q)))
          (f 1₂) refl)
        (f 0₂) refl , isequiv-prop _ _)
      where open qinv (isequiv→qinv e)

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

module Exercise15 {i j} {A : 𝒰 i} {B : A → 𝒰 j} {x y : A} {p : x == y} {u : B x}
  where
  _ : transport _ p == transport id (ap B p)
  _ = =-ind (λ _ _ p → transport _ p == transport id (ap B p)) (λ _ → refl) p

module Exercise16 {i} {j} {A : 𝒰 i} {B : A → 𝒰 j} (f g : Π A B) where
  open import HoTT.Identity
  open import HoTT.Identity.Sigma
  open import HoTT.Identity.Pi using (funext)
  open import HoTT.Equivalence

  =Π-equiv : f == g ≃ f ~ g
  =Π-equiv = happly , qinv→isequiv (funext' , η , ε)
    where
    -- Define funext' in such a way that funext (happly refl) ≡
    -- funext (λ x. refl) can cancel.
    funext' : {g : Π A B} → f ~ g → f == g
    funext' α = funext α ∙ funext (λ _ → refl) ⁻¹
    η : funext' ∘ happly ~ id
    η refl = invᵣ
    ε : happly ∘ funext' ~ id
    ε α = transport P p (ap happly invᵣ)
      where
      P : Π[ x ∶ A ] Σ[ y ∶ B x ] f x == y → 𝒰 _
      P h = let α = pr₂ ∘ h in happly (funext' α) == α
      -- The trick here is to use funext to simultaneously show
      -- that λ x. (f x , refl) = λ x. (g x , α x). Then, we can
      -- transport a path made by canceling the funext with its
      -- inverse to get the desired equality.
      p : (λ x → f x , refl) == (λ x → g x , α x)
      p = funext λ x → pair⁼ (α x , =-ind (λ _ _ p → transport _ p refl == p) (λ _ → refl) (α x))

module Exercise17 {i} where
  open import HoTT.Equivalence
  open import HoTT.Equivalence.Proposition
  open import HoTT.Identity.Product
  open import HoTT.Identity.Sigma
  open import HoTT.Identity.Universe
  open import HoTT.Identity.Pi

  variable
    A A' B B' : 𝒰 i
    P : A → 𝒰 i
    P' : A' → 𝒰 i

  prop : (_◆_ : 𝒰 i → 𝒰 i → 𝒰 i) → A == A' → B == B' → (A ◆ B) ≃ (A' ◆ B')
  prop {A} {A'} {B} {B'} (_◆_) p q =
    transport (λ{ (A' , B') → A ◆ B ≃ A' ◆ B' })
      (×-pair⁼ {x = A , B} {y = A' , B'} (p , q)) reflₑ

  module _ (e₁ : A ≃ A') (e₂ : B ≃ B')
    where
    open Iso (eqv→iso e₁) renaming (f to f₁ ; g to g₁ ; η to η₁ ; ε to ε₁)
    open Iso (eqv→iso e₂) renaming (f to f₂ ; g to g₂ ; η to η₂ ; ε to ε₂)

    -- (i) Proof without using univalence
    prop-×' : A × B ≃ A' × B'
    prop-×' = let open Iso in iso→eqv λ where
      .f (a , b) → f₁ a , f₂ b
      .g (a' , b') → g₁ a' , g₂ b'
      .η (a , b) → ×-pair⁼ (η₁ a , η₂ b)
      .ε (a' , b') → ×-pair⁼ (ε₁ a' , ε₂ b')

    -- (ii) Proof using univalence (for general operator)
    prop-× = prop _×_ (ua e₁) (ua e₂)

    -- (iii) Proof for non-dependent type formers (→, +)
    prop-→ = prop (λ A B → A → B) (ua e₁) (ua e₂)
    prop-+ = prop _+_ (ua e₁) (ua e₂)

  -- Proof that (i) and (ii) are equal
  propᵢ₌ᵢᵢ : (e₁ : A ≃ A') (e₂ : B ≃ B') → prop-×' e₁ e₂ == prop-× e₁ e₂
  propᵢ₌ᵢᵢ e₁ e₂ = ap² prop-×' (=𝒰-β e₁ ⁻¹) (=𝒰-β e₂ ⁻¹) ∙ lemma
    where
    lemma : prop-×' (idtoeqv (ua e₁)) (idtoeqv (ua e₂)) == prop-× e₁ e₂
    lemma rewrite ua e₁ rewrite ua e₂ =
      pair⁼ (funext (λ{ (a , b) → refl }) , isequiv-prop _ _)

  module _ (e₁ : A ≃ A') (e₂ : (x : A') → transport (λ A' → A' → 𝒰 i) (ua e₁) P x ≃ P' x)
    where
    prop-dep : (_◆_ : (A : 𝒰 i) → (A → 𝒰 i) → 𝒰 i) → (A ◆ P) ≃ (A' ◆ P')
    prop-dep _◆_ = transport (λ{ (A' , P') → A ◆ P ≃ A' ◆ P' })
      (pair⁼ {x = A , P} {y = A' , P'} (ua e₁ , funext (ua ∘ e₂))) reflₑ

    -- (iii) Proof for dependent type formers (Σ, Π)
    prop-Σ = prop-dep Σ
    prop-Π = prop-dep Π

module Exercise18 {i} {A : 𝒰 i} {B : A → 𝒰 i} {f g : Π A B} {H : f ~ g}
                  {x y : A} {p : x == y}
  where
  -- We first induct on p, changing our goal to
  --
  --   ap (transport refl) (H x) ∙ apd g refl = apd f refl ∙ H y
  --
  -- This reduces to
  --
  --   ap id (H x) ∙ refl = refl ∙ H x
  --
  -- Now, we just need one final induction on H x, after which our goal
  -- reduces to refl : refl = refl.
  _ : ap (transport _ p) (H x) ∙ apd g p == apd f p ∙ H y
  _ = =-ind' (λ y p → ap (transport _ p) (H x) ∙ apd g p == apd f p ∙ H y)
    (=-ind' (λ _ Hₓ → ap id Hₓ ∙ refl == refl ∙ Hₓ) refl (H x)) p
