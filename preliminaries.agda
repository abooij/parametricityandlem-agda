{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module preliminaries where

U = Type lzero
LEM = (P : U) → is-prop P → P ⊔ ¬ P
WEM = (A : U) → ¬ A ⊔ ¬ (¬ A)

endomap-natural : (f : (X : U) → X → X) → Type (lsucc lzero)
endomap-natural f = (X Y : U) → (e : X ≃ Y) → (x : X)→  –> e (f X x) == f Y (–> e x)

dec-natural : (f : (X : U) → X → Bool) → Type (lsucc lzero)
dec-natural f = (X Y : U) → (e : X ≃ Y) → (x : X) → f Y (–> e x) == f X x

equiv-invariant : (f : U → U) → Type (lsucc lzero)
equiv-invariant f = {X Y : U} → X ≃ Y → f X ≃ f Y

pointed-invariant : (f : (X : U) → X → U) → Type (lsucc lzero)
pointed-invariant f = {X Y : U} → (e : X ≃ Y) → (x : X) → f X x ≃ f Y (–> e x)

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
  (λ {(y , yp) → (<– e y) , (λ x → ap (<– e) (yp (–> e x)) ∙ <–-inv-l e x)})
  (λ b → prop-has-all-paths is-contr-is-prop _ _)
  (λ b → prop-has-all-paths is-contr-is-prop _ _)

is-prop-equiv : {{_ : FUNEXT}} → ∀ {i} {X Y : Type i} → X ≃ Y → is-prop X → is-prop Y
is-prop-equiv e X-prop = all-paths-is-prop (λ y y' →
  y =⟨ ! (<–-inv-r e y) ⟩
  –> e (<– e y) =⟨ prop-has-all-paths X-prop _ _ |in-ctx (–> e) ⟩
  –> e (<– e y') =⟨ <–-inv-r e y' ⟩
  y' =∎)

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

×-Unit-r : ∀ {i} {A : Type i} → A × Unit ≃ A
×-Unit-r = ×-Unit ∘e ×-comm

×-Empty : ∀ {i} {A : Type i} → Empty × A ≃ Empty
×-Empty = Σ₁-Empty

⊔-comm : ∀ {i j} {A : Type i} {B : Type j} → A ⊔ B ≃ B ⊔ A
⊔-comm {A = A} {B = B} = equiv to from from-to to-from
  where
  to : A ⊔ B → B ⊔ A
  to (inl a) = inr a
  to (inr b) = inl b
  from : B ⊔ A → A ⊔ B
  from (inl b) = inr b
  from (inr a) = inl a
  to-from : ∀ ab → from (to ab) == ab
  to-from (inl a) = idp
  to-from (inr b) = idp
  from-to : ∀ ba → to (from ba) == ba
  from-to (inl b) = idp
  from-to (inr a) = idp

⊔-Empty : ∀ {i} {A : Type i} → A ⊔ Empty ≃ A
⊔-Empty {A = A} = equiv to from from-to to-from
  where
  to : A ⊔ Empty → A
  to (inl x) = x
  to (inr ())
  from : A → A ⊔ Empty
  from a = inl a
  to-from : ∀ au → from (to au) == au
  to-from (inl x) = idp
  to-from (inr ())
  from-to : ∀ a → to (from a) == a
  from-to a = idp

⊔-Empty-l : ∀ {i} {A : Type i} → Empty ⊔ A ≃ A
⊔-Empty-l = ⊔-Empty ∘e ⊔-comm

is-left : ∀ {i} {A B : Type i} → A ⊔ B → Bool
is-left (inl _) = true
is-left (inr _) = false

is-right : ∀ {i} {A B : Type i} → A ⊔ B → Bool
is-right (inl _) = false
is-right (inr _) = true

¬-is-prop0 : {{_ : FUNEXT0}} → {A : U} → is-prop (¬ A)
¬-is-prop0 {A} = all-paths-is-prop (λ x y → λ=0)

inhab-¬-Empty : {{_ : FUNEXT}} → ∀ {i} {A : Type i} → A → ¬ A ≃ Empty
inhab-¬-Empty {A = A} a = equiv to from from-to to-from
  where
  to : ¬ A → Empty
  to negA = negA a
  from : Empty → ¬ A
  from ()
  to-from : ∀ negA → from (to negA) == negA
  to-from negA = λ= (⊥-rec ∘ negA)
  from-to : ∀ u → to (from u) == u
  from-to ()

inhab-¬-Empty0 : {{_ : FUNEXT0}} → ∀ {i} {A : Type i} → A → ¬ A ≃ Empty
inhab-¬-Empty0 {A = A} a = equiv to from from-to to-from
  where
  to : ¬ A → Empty
  to negA = negA a
  from : Empty → ¬ A
  from ()
  to-from : ∀ negA → from (to negA) == negA
  to-from negA = λ=0
  from-to : ∀ u → to (from u) == u
  from-to ()

prop-equiv : ∀ {i} {A B : Type i} → is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
prop-equiv A-is-prop B-is-prop f g =
  equiv f g
    (λ b → prop-has-all-paths B-is-prop _ _)
    (λ a → prop-has-all-paths A-is-prop _ _)

contra : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → ¬ B → ¬ A
contra f negB a = negB (f a)

[[]]-equiv : {{_ : PTRUNC}} → ∀ {i} {A B : Type i} → (A → B) → (B → A) → [[ A ]] ≃ [[ B ]]
[[]]-equiv f g =
  prop-equiv PTrunc-level PTrunc-level
    (PTrunc-rec PTrunc-level (p[_] ∘ f))
    (PTrunc-rec PTrunc-level (p[_] ∘ g))

[[]]≃ : {{_ : PTRUNC}} → ∀ {i} {A B : Type i} → A ≃ B → [[ A ]] ≃ [[ B ]]
[[]]≃ e = [[]]-equiv (–> e) (<– e)

[[]]μ : {{_ : PTRUNC }} → ∀ {i} {A : Type i} → [[ [[ A ]] ]] ≃ [[ A ]]
[[]]μ = equiv
  (PTrunc-rec PTrunc-level (idf _))
  p[_]
  (λ b → prop-has-all-paths PTrunc-level _ _)
  (λ c → prop-has-all-paths PTrunc-level _ _)

inhab-prop-equiv-Unit : ∀ {i} {A : Type i} → A → is-prop A → A ≃ Unit
inhab-prop-equiv-Unit a A-is-prop = contr-equiv-Unit (inhab-prop-is-contr a A-is-prop)

component-is-prop : {{_ : FUNEXT}} {{_ : PTRUNC}} → ∀ {i} {A : Type i} → (a : A) → is-prop (a == a) → is-contr (Σ A λ a' → [[ a == a' ]])
component-is-prop {A = A} a a-is-prop = inhab-prop-is-contr (a , p[ idp ]) prop
  where
  go : has-all-paths (Σ A λ a' → [[ a == a' ]])
  go (a' , p) (a'' , q) = pair= (! a'-path ∙ a''-path) (prop-has-all-paths-↓ PTrunc-level)
    where
    a'-is-prop : is-prop (a == a')
    a'-is-prop = PTrunc-rec is-prop-is-prop (λ r → is-prop-equiv (post∙-equiv r) a-is-prop) p
    a''-is-prop : is-prop (a == a'')
    a''-is-prop = PTrunc-rec is-prop-is-prop (λ r → is-prop-equiv (post∙-equiv r) a-is-prop) q
    a'-path : a == a'
    a'-path = PTrunc-rec a'-is-prop (idf _) p
    a''-path : a == a''
    a''-path = PTrunc-rec a''-is-prop (idf _) q
  prop : is-prop (Σ A λ a' → [[ a == a' ]])
  prop = all-paths-is-prop go

prop-dec-is-prop : {{_ : FUNEXT}} (P : U) → is-prop P → is-prop (P ⊔ ¬ P)
prop-dec-is-prop P P-is-prop = all-paths-is-prop go
  where
  P-paths : has-all-paths P
  P-paths = prop-has-all-paths P-is-prop
  ¬P-paths : has-all-paths (¬ P)
  ¬P-paths = prop-has-all-paths ¬-is-prop
  go : has-all-paths (P ⊔ ¬ P)
  go (inl x₁) (inl x₂) = P-paths _ _ |in-ctx inl
  go (inl x₁) (inr x₂) with x₂ x₁
  go (inl x₁) (inr x₂) | ()
  go (inr x₁) (inl x₂) with x₁ x₂
  go (inr x₁) (inl x₂) | ()
  go (inr x₁) (inr x₂) = ¬P-paths _ _ |in-ctx inr

prop-dec-is-prop0 : {{_ : FUNEXT0}} (P : U) → is-prop P → is-prop (P ⊔ ¬ P)
prop-dec-is-prop0 P P-is-prop = all-paths-is-prop go
  where
  P-paths : has-all-paths P
  P-paths = prop-has-all-paths P-is-prop
  ¬P-paths : has-all-paths (¬ P)
  ¬P-paths = prop-has-all-paths ¬-is-prop0
  go : has-all-paths (P ⊔ ¬ P)
  go (inl x₁) (inl x₂) = P-paths _ _ |in-ctx inl
  go (inl x₁) (inr x₂) with x₂ x₁
  go (inl x₁) (inr x₂) | ()
  go (inr x₁) (inl x₂) with x₁ x₂
  go (inr x₁) (inl x₂) | ()
  go (inr x₁) (inr x₂) = ¬P-paths _ _ |in-ctx inr

singleton-equiv-Unit : ∀ {i} → {A : Type i} → (a : A) → (Σ A λ a' → a == a') ≃ Unit
singleton-equiv-Unit a = contr-equiv-Unit (pathfrom-is-contr a)

join-Empty-idem : {{_ : PUSHOUT}} → ∀ {i} → {A : Type i} → A * Empty ≃ A
join-Empty-idem {A = A} = equiv to from from-to to-from
  where
  to : A * Empty → A
  to = Join-rec (idf _) ⊥-rec (λ a → ⊥-elim)
  from : A → A * Empty
  from = jleft
  to-from : ∀ ae → from (to ae) == ae
  to-from = Join-elim (λ a → idp) ⊥-elim (λ a → ⊥-elim)
  from-to : ∀ a → to (from a) == a
  from-to a = idp

join-Unit-idem : {{_ : PUSHOUT}} → ∀ {i} → {A : Type i} → A * Unit ≃ Unit
join-Unit-idem {A = A} = equiv to from from-to to-from
  where
  to : A * Unit → Unit
  to _ = unit
  from : Unit → A * Unit
  from _ = jright unit
  lem : {x y : A * Unit} → (p : x == y) → (u : from (to x) == x) →
    transport (λ z → from (to z) == z) p u == ! (ap (from ∘ to) p) ∙ u ∙ p
  lem idp u = ! (∙-unit-r u)
  lem' : ∀ a → ! (ap (from ∘ to) (jglue a unit)) ∙ ! (jglue a unit) ∙ (jglue a unit) == idp
  lem' a =
    ! (ap (from ∘ to) (jglue a unit)) ∙ (! (jglue a unit) ∙ jglue a unit)
      =⟨ ap ! (ap-cst (jright unit) (jglue a unit)) ∙2 !-inv-l (jglue a unit) ⟩
    idp ∙ idp
      =⟨ idp ⟩
    idp
      =∎
  to-from : ∀ au → from (to au) == au
  to-from = Pushout-elim
    (λ a → ! (jglue a unit))
    (λ {unit → idp})
    (λ {(a , unit) → from-transp
      (λ z → from (to z) == z)
      (jglue a unit)
      (lem (jglue a unit) (! (jglue a unit)) ∙ lem' a)})
  from-to : ∀ u → to (from u) == u
  from-to unit = idp
