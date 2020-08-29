{-# OPTIONS --without-K #-}
open import HoTT.Base
open import HoTT.Identity
open import HoTT.Identity.Boolean
open import HoTT.Identity.Coproduct
open import HoTT.Identity.Sigma
open import HoTT.Identity.Identity
open import HoTT.Identity.Pi
open import HoTT.Identity.NaturalNumber
open import HoTT.Transport.Identity
open import HoTT.Equivalence
open import HoTT.Equivalence.Lift
open import HoTT.Equivalence.Transport
open import HoTT.Homotopy

module HoTT.HLevel where

open variables
private variable n : ℕ

isContr : 𝒰 i → 𝒰 i
isContr A = Σ[ a ∶ A ] Π[ x ∶ A ] (a == x)

-- Use a record so that we can use instances (technique from HoTT-Agda)
record hlevel (n : ℕ) (A : 𝒰 i) : 𝒰 i

hlevel-type : ℕ → 𝒰 i → 𝒰 i
hlevel-type zero = isContr
hlevel-type (succ n) A = {x y : A} → hlevel n (x == y)

record hlevel n A where
  inductive
  eta-equality
  constructor hlevel-in
  field hlevel-out : hlevel-type n A
open hlevel public

center : ⦃ hlevel 0 A ⦄ → A
center ⦃ hlevel-in (c , _) ⦄ = c

contr : ⦃ _ : hlevel 0 A ⦄ {x : A} → center == x
contr ⦃ hlevel-in (_ , p) ⦄ = p _

isProp : 𝒰 i → 𝒰 i
isProp A = (x y : A) → x == y

record hlevel𝒰 (n : ℕ) (i : _) : 𝒰 (lsuc i) where
  constructor type
  infix 90 _ty
  field
    _ty : 𝒰 i
    ⦃ h ⦄ : hlevel n _ty
open hlevel𝒰 using (_ty) public

Prop𝒰 = hlevel𝒰 1
Prop𝒰₀ = Prop𝒰 lzero

isSet : 𝒰 i → 𝒰 i
isSet A = {x y : A} → isProp (x == y)

Set𝒰 = hlevel𝒰 2
Set𝒰₀ = Set𝒰 lzero

instance
  =-hlevel : {x y : A} → ⦃ hlevel (succ n) A ⦄ → hlevel n (x == y)
  =-hlevel ⦃ hlevel-in h ⦄ = h

_◃_ : 𝒰 i → 𝒰 j → 𝒰 (i ⊔ j)
A ◃ B = Σ (A → B) rinv
infixr 5 _◃_

-- Theorem 7.1.4
retract-hlevel : A ◃ B → ⦃ hlevel n A ⦄ → hlevel n B
retract-hlevel {n = zero} (p , s , ε) = hlevel-in (p center , λ b → ap p contr ∙ ε b)
retract-hlevel {A = A} {B = B} {n = succ n} (p , s , ε) =
  hlevel-in (retract-hlevel {n = n} r)
  where
  -- t =
  r : {y y' : B} → (s y == s y') ◃ (y == y')
  r {y} {y'} = t , ap s , λ u →
    ε y ⁻¹ ∙ ap p (ap s u) ∙ ε y'  =⟨ _ ∙ₗ ap-∘ p s u ⁻¹ ∙ᵣ _ ⟩
    ε y ⁻¹ ∙ ap (p ∘ s) u ∙ ε y'   =⟨ assoc ⁻¹ ⟩
    ε y ⁻¹ ∙ (ap (p ∘ s) u ∙ ε y') =⟨ pivotₗ (~-natural-id ε u) ⁻¹ ⟩
    u                              ∎
    where
    open =-Reasoning
    t : _
    t q = ε y ⁻¹ ∙ ap p q ∙ ε y'

equiv-hlevel : A ≃ B → ⦃ hlevel n A ⦄ → hlevel n B
equiv-hlevel e = retract-hlevel (pr₁ e , qinv→rinv (isequiv→qinv (pr₂ e)))

Π-implicit-equiv : ({x : A} → P x) ≃ Π A P
Π-implicit-equiv = iso→eqv λ{.f x _ → x ; .g h → h _ ; .η _ → refl ; .ε _ → refl}
  where open Iso

raise : ⦃ {_ : A} → hlevel n A ⦄ → hlevel (succ n) A
raise {n = zero} ⦃ f ⦄ = hlevel-in λ {x} →
  hlevel-in (contr ⦃ f {x} ⦄ ⁻¹ ∙ contr , λ{refl → invₗ})
raise {n = succ n} ⦃ f ⦄ = hlevel-in λ {x} →
  raise ⦃ =-hlevel ⦃ f {x} ⦄ ⦄

add : ℕ → ℕ → ℕ
add n zero = n
add n (succ m) = succ (add n m)

raise* : {A : 𝒰 i} → ⦃ hlevel n A ⦄ → {m : ℕ} → hlevel (add n (succ m)) A
raise* {m = zero} = raise
raise* {m = succ m} = raise ⦃ raise* ⦄

instance
  Lift-hlevel : ⦃ hlevel n A ⦄ → hlevel n (Lift {i} A)
  Lift-hlevel = equiv-hlevel (Lift-equiv ⁻¹ₑ)

  𝟎-hlevel : hlevel (succ n) (𝟎 {i})
  𝟎-hlevel {zero} = hlevel-in λ where {()}
  𝟎-hlevel {succ _} = raise

  𝟏-hlevel : hlevel n (𝟏 {i})
  𝟏-hlevel {zero} = hlevel-in (★ , λ where ★ → refl)
  𝟏-hlevel {succ _} = raise

  𝟐-hlevel : hlevel (succ (succ n)) 𝟐
  𝟐-hlevel {n} = hlevel-in (equiv-hlevel (=𝟐-equiv ⁻¹ₑ))
    where
    code-hlevel : {x y : 𝟐} → hlevel (succ n) (x =𝟐 y)
    code-hlevel {0₂} {0₂} = ⟨⟩
    code-hlevel {0₂} {1₂} = ⟨⟩
    code-hlevel {1₂} {0₂} = ⟨⟩
    code-hlevel {1₂} {1₂} = ⟨⟩
    instance _ = code-hlevel

  Π-hlevel : ⦃ {x : A} → hlevel n (P x) ⦄ → hlevel n (Π A P)
  Π-hlevel {n = zero} = hlevel-in ((λ _ → center) , (λ _ → funext λ _ → contr))
  Π-hlevel {n = succ n} = hlevel-in (equiv-hlevel (=Π-equiv ⁻¹ₑ))

  Π-implicit-hlevel : ⦃ {x : A} → hlevel n (P x) ⦄ → hlevel n ({x : A} → P x)
  Π-implicit-hlevel = equiv-hlevel (Π-implicit-equiv ⁻¹ₑ)

  +-hlevel : ⦃ hlevel (succ (succ n)) A ⦄ → ⦃ hlevel (succ (succ n)) B ⦄ →
             hlevel (succ (succ n)) (A + B)
  +-hlevel {n} {A = A} {B = B} = hlevel-in (equiv-hlevel (=+-equiv ⁻¹ₑ))
    where
    code-hlevel : {x y : A + B} → hlevel (succ n) (x =+ y)
    code-hlevel {inl _} {inl _} = ⟨⟩
    code-hlevel {inl _} {inr _} = ⟨⟩
    code-hlevel {inr _} {inl _} = ⟨⟩
    code-hlevel {inr _} {inr _} = ⟨⟩
    instance _ = code-hlevel

  ℕ-hlevel : hlevel 2 ℕ
  hlevel-out ℕ-hlevel {x} = equiv-hlevel (=ℕ-equiv ⁻¹ₑ)
    where
    code-hlevel : {x y : ℕ} → hlevel 1 (x =ℕ y)
    code-hlevel {zero} {zero} = ⟨⟩
    code-hlevel {zero} {succ y} = ⟨⟩
    code-hlevel {succ x} {zero} = ⟨⟩
    code-hlevel {succ x} {succ y} = code-hlevel {x}
    instance _ = code-hlevel {x}

-- Make Σ-hlevel a private instance so it can be installed as-needed.
-- There are too many cases where we want to use some other instance
-- instead.
Σ-hlevel : ⦃ h₁ : hlevel n A ⦄ → ⦃ h₂ : {x : A} → hlevel n (P x) ⦄ → hlevel n (Σ A P)
private instance _ = Σ-hlevel
Σ-hlevel {n = zero} = hlevel-in ((center , center) , λ x → pair⁼' (contr , contr))
Σ-hlevel {n = succ n} = hlevel-in (equiv-hlevel (=Σ-equiv ⁻¹ₑ))

→-hlevel : ⦃ hlevel n B ⦄ → hlevel n (A → B)
→-hlevel = ⟨⟩

×-hlevel : ⦃ h₁ : hlevel n A ⦄ → ⦃ h₂ : hlevel n B ⦄ → hlevel n (A × B)
×-hlevel = ⟨⟩

isContr-hlevel : hlevel 1 (isContr A)
hlevel-out (isContr-hlevel {A = A}) {h} = ⟨⟩
  where instance _ = raise* ⦃ hlevel-in h ⦄

hlevel-equiv : hlevel-type n A ≃ hlevel n A
hlevel-equiv = hlevel-in , qinv→isequiv (hlevel-out , (λ _ → refl) , (λ _ → refl))

instance
  hlevel-hlevel : hlevel 1 (hlevel n A)
  hlevel-hlevel {zero} = equiv-hlevel hlevel-equiv ⦃ isContr-hlevel ⦄
  hlevel-hlevel {succ n} = equiv-hlevel hlevel-equiv

hlevel⁼ : ⦃ h₁ : hlevel n A ⦄ ⦃ h₂ : hlevel n B ⦄ → A == B → type A == type B
hlevel⁼ ⦃ h₁ ⦄ ⦃ h₂ ⦄ refl rewrite center ⦃ =-hlevel {x = h₁} {h₂} ⦄ = refl

hlevel1→isProp : ⦃ hlevel 1 A ⦄ → isProp A
hlevel1→isProp = center

hlevel2→isSet : ⦃ hlevel 2 A ⦄ → isSet A
hlevel2→isSet = center

isProp→hlevel1 : isProp A → hlevel 1 A
hlevel-out (isProp→hlevel1 f) {x} {y} = ⟨⟩
  where instance _ = raise ⦃ hlevel-in (x , f x) ⦄

isProp-hlevel1 : hlevel 1 (isProp A)
hlevel-out isProp-hlevel1 {f} = ⟨⟩
  where instance _ = raise ⦃ isProp→hlevel1 f ⦄

isProp-prop : isProp (isProp A)
isProp-prop = hlevel1→isProp ⦃ isProp-hlevel1 ⦄

isProp→isSet : isProp A → isSet A
isProp→isSet A-prop {x} {y} p q = center
  where instance _ = raise ⦃ isProp→hlevel1 A-prop ⦄

isContr-prop : isProp (isContr A)
isContr-prop (a , p) (a' , p') = pair⁼ (p a' , center)
  where instance _ = raise* ⦃ hlevel-in (a , p) ⦄

prop-equiv : ⦃ h₁ : hlevel 1 A ⦄ → ⦃ h₂ : hlevel 1 B ⦄ →
             (A → B) → (B → A) → A ≃ B
prop-equiv f g = f , qinv→isequiv (g , (λ _ → center) , (λ _ → center))

Σ-contr₁ : ⦃ _ : hlevel 0 A ⦄ → Σ A P ≃ P center
Σ-contr₁ {A = A} {P = P} ⦃ h ⦄ = let open Iso in iso→eqv λ where
  .f   → transport P (contr ⁻¹) ∘ pr₂
  .g y → center , y
  .η x → pair⁼ (contr , Eqv.ε (transport-equiv (contr {A = A})) _)
  .ε y → ap {x = contr ⁻¹} (λ p → transport P p y)
    let instance _ = raise* ⦃ h ⦄ in center

Σ-contr₂ : ⦃ {x : A} → hlevel 0 (P x) ⦄ → Σ A P ≃ A
Σ-contr₂ = let open Iso in iso→eqv λ where
  .f   → pr₁
  .g x → x , center
  .η _ → pair⁼ (refl , contr)
  .ε _ → refl

×-contr₁ : ⦃ hlevel 0 A ⦄ → A × B ≃ B
×-contr₁ = Σ-contr₁

×-contr₂ : ⦃ hlevel 0 B ⦄ → A × B ≃ A
×-contr₂ = Σ-contr₂

Π-contr₁ : ⦃ _ : hlevel 0 A ⦄ → Π A P ≃ P center
Π-contr₁ {A = A} {P = P} ⦃ h ⦄ = let open Iso in iso→eqv λ where
  .f h   → h center
  .g x _ → transport P contr x
  .η h   → funext (λ _ → apd h contr)
  .ε x   → ap {x = contr} (λ p → transport P p x)
    let instance _ = raise* ⦃ h ⦄ in center

=-contrₗ : (a : A) → hlevel 0 (Σ A (a ==_))
=-contrₗ a = hlevel-in ((a , refl) , λ (_ , p) →
  pair⁼ (p , transport=-const-id p a refl ∙ unitₗ ⁻¹))

=-contrᵣ : (a : A) → hlevel 0 (Σ A (_== a))
=-contrᵣ a = hlevel-in ((a , refl) , λ (_ , p) →
  pair⁼ (p ⁻¹ , transport=-id-const a (p ⁻¹) refl ∙ unitᵣ ⁻¹ ∙ invinv))
