{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module preliminaries where

U = Type lzero
LEM = (P : U) → is-prop P → P ⊔ ¬ P

endomap-natural : (f : (X : U) → X → X) → Type (lsucc lzero)
endomap-natural f = (X Y : U) → (e : X ≃ Y) → (x : X)→  –> e (f X x) == f Y (–> e x)

data Singleton {i} {A : Set i} (x : A) : Set i where
  _with≡_ : (y : A) → x == y → Singleton x

inspect : ∀ {i} {A : Set i} (x : A) → Singleton x
inspect x = x with≡ idp

–>-preserves-≠ : {X Y : U} → (e : X ≃ Y) → {x x' : X} → x ≠ x' → –> e x ≠ –> e x'
–>-preserves-≠ e = inj-preserves-≠ (–>-is-inj e)

<–-preserves-≠ : {X Y : U} → (e : X ≃ Y) → {y y' : Y} → y ≠ y' → <– e y ≠ <– e y'
<–-preserves-≠ e = inj-preserves-≠ (–>-is-inj (e ⁻¹))

is-contr-equiv : {{_ : FUNEXT}} {X Y : U} → X ≃ Y → is-contr X ≃ is-contr Y
is-contr-equiv e = equiv
  (λ {(x , xp) → (–> e x) , (λ y → ap (–> e) (xp (<– e y)) ∙ <–-inv-r e y)})
  ((λ {(y , yp) → (<– e y) , (λ x → ap (<– e) (yp (–> e x)) ∙ <–-inv-l e x)}))
  (λ b → prop-has-all-paths is-contr-is-prop _ _)
  (λ b → prop-has-all-paths is-contr-is-prop _ _)

isolated : {X : U} → (x : X) → U
isolated {X} x = (y : X) → (x == y) ⊔ (x ≠ y)

infix 20 _⇔_

_⇔_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A ⇔ B = (A → B) × (B → A)

×≃ : ∀ {i} {A B C D : Type i} → A ≃ B → C ≃ D → A × C ≃ B × D
×≃ {_} {A} {B} {C} {D} e f = equiv to from from-to to-from
  where
  to : A × C → B × D
  to (a , c) = (–> e a) , (–> f c)
  from : B × D → A × C
  from (b , d) = (<– e b) , (<– f d)
  to-from : (ac : A × C) → from (to ac) == ac
  to-from (a , c) = pair×= (<–-inv-l e a) (<–-inv-l f c)
  from-to : (bd : B × D) → to (from bd) == bd
  from-to (b , d) = pair×= (<–-inv-r e b) (<–-inv-r f d)

⊔≃ : ∀ {i} {A B C D : Type i} → A ≃ B → C ≃ D → A ⊔ C ≃ B ⊔ D
⊔≃ {_} {A} {B} {C} {D} e f = equiv to from from-to to-from
  where
  to : A ⊔ C → B ⊔ D
  to (inl a) = inl (–> e a)
  to (inr c) = inr (–> f c)
  from : B ⊔ D → A ⊔ C
  from (inl b) = inl (<– e b)
  from (inr d) = inr (<– f d)
  to-from : (ac : A ⊔ C) → from (to ac) == ac
  to-from (inl a) = ap inl (<–-inv-l e a)
  to-from (inr c) = ap inr (<–-inv-l f c)
  from-to : (bd : B ⊔ D) → to (from bd) == bd
  from-to (inl b) = ap inl (<–-inv-r e b)
  from-to (inr d) = ap inr (<–-inv-r f d)

×-Unit : ∀ {i} {A : Type i} → Unit × A ≃ A
×-Unit = Σ₁-Unit

is-left : ∀ {i} {A B : Type i} → A ⊔ B → Bool
is-left (inl _) = true
is-left (inr _) = false
