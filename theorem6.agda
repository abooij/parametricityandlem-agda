{-# OPTIONS --without-K --rewriting #-}

module theorem6 where

open import HoTT
open import preliminaries
open import lemma2

theorem-6-A : {{_ : FUNEXT0}} → ∀ {i} →
  (f : (X : Type i) → X → Bool) →
  dec-natural f →
  (X Y : Type i) → (x : X) → isolated x → (y : Y) → isolated y →
  f X x ≠ f Y y → WEM i
theorem-6-A {i = i} f f-nat X Y x x-isol y y-isol ineq A = claim-E
  where
  wlog-X : Σ (Type i) λ X' → Σ X' λ x' → isolated x' × (f X' x' == true)
  wlog-X with inspect (f X x)
  wlog-X | true  with≡ p = X , (x , (x-isol , p))
  wlog-X | false with≡ p with inspect (f Y y)
  wlog-X | false with≡ p | false with≡ q = ⊥-rec (ineq (p ∙ ! q))
  wlog-X | false with≡ p | true  with≡ q = Y , (y , (y-isol , q))
  wlog-Y : Σ (Type i) λ Y' → Σ Y' λ y' → isolated y' × (f Y' y' == false)
  wlog-Y with inspect (f Y y)
  wlog-Y | false with≡ p = Y , (y , (y-isol , p))
  wlog-Y | true  with≡ p with inspect (f X x)
  wlog-Y | true  with≡ p | true  with≡ q = ⊥-rec (ineq (q ∙ ! p))
  wlog-Y | true  with≡ p | false with≡ q = X , (x , (x-isol , q))
  X^ : Type i
  X^ = fst wlog-X
  x^ : X^
  x^ = fst (snd wlog-X)
  x^-isol : isolated x^
  x^-isol = fst (snd (snd wlog-X))
  f-x^ : f X^ x^ == true
  f-x^ = snd (snd (snd wlog-X))
  Y^ : Type i
  Y^ = fst wlog-Y
  y^ : Y^
  y^ = fst (snd wlog-Y)
  y^-isol : isolated y^
  y^-isol = fst (snd (snd wlog-Y))
  f-y^ : f Y^ y^ == false
  f-y^ = snd (snd (snd wlog-Y))
  X' : Type i
  X' = fst (fst (fst (lemma-2 x^) x^-isol))
  X'-e : X^ ≃ X' ⊔ Unit
  X'-e = snd (fst (fst (lemma-2 x^) x^-isol))
  Y' : Type i
  Y' = fst (fst (fst (lemma-2 y^) y^-isol))
  Y'-e : Y^ ≃ Y' ⊔ Unit
  Y'-e = snd (fst (fst (lemma-2 y^) y^-isol))
  Z : Type i
  Z = (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y'))
  z : Z
  z = (inl unit) , (inl unit)
  claim-A : ¬ A → Z ≃ X^
  claim-A negA =
    (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y'))
      ≃⟨ ×≃
        (⊔≃ (ide Unit) (×≃ (contr-equiv-Unit (inhab-prop-is-contr negA ¬-is-prop0) ) (ide _)))
        (⊔≃ (ide Unit) (×≃ (inhab-¬-Empty0 negA) (ide _)))
       ⟩
    (Unit ⊔ (Unit × X')) × (Unit ⊔ (Empty × Y'))
      ≃⟨ ×≃
        (⊔≃ (ide Unit) ×-Unit)
        (⊔≃ (ide Unit) ×-Empty)
       ⟩
    (Unit ⊔ X') × (Unit ⊔ Empty)
      ≃⟨ ×≃ (X'-e ⁻¹ ∘e ⊔-comm) ⊔-Empty ⟩
    X^ × Unit
      ≃⟨ ×-Unit-r ⟩
    X^ ≃∎
  claim-B : ¬ A → f Z z == true
  claim-B negA = ! (f-nat Z X^ (claim-A negA) z) ∙ f-x^
  claim-C : A → Z ≃ Y^
  claim-C a =
    (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y')) ≃⟨
      ×≃
        (⊔≃ (ide Unit) (×≃ {i = i} (inhab-¬-Empty0 a) (ide X')))
        (⊔≃ (ide Unit) (×≃ (contr-equiv-Unit (inhab-prop-is-contr (λ x₁ → x₁ a) ¬-is-prop0)) (ide Y')))
      ⟩
    (Unit ⊔ (Empty × X')) × (Unit ⊔ (Unit × Y'))
      ≃⟨
        ×≃ (⊔≃ (ide Unit) ×-Empty) (⊔≃ (ide Unit) ×-Unit)
       ⟩
    (Unit ⊔ Empty) × (Unit ⊔ Y')
      ≃⟨
        ×≃ ⊔-Empty (Y'-e ⁻¹ ∘e ⊔-comm)
       ⟩
    Unit × Y^
      ≃⟨ ×-Unit ⟩
    Y^ ≃∎
  claim-D : A → f Z z == false
  claim-D a = ! (f-nat Z Y^ (claim-C a) z) ∙ f-y^
  claim-B-contra : f Z z == false → ¬ (¬ A)
  claim-B-contra p = λ negA → Bool-true≠false (! (claim-B negA) ∙ p)
  claim-D-contra : f Z z == true → ¬ A
  claim-D-contra p = λ a → Bool-false≠true (! (claim-D a) ∙ p)
  claim-E : ¬ A ⊔ ¬ (¬ A)
  claim-E with inspect (f Z z)
  claim-E | true with≡ x₂ = inl (claim-D-contra x₂)
  claim-E | false with≡ x₂ = inr (claim-B-contra x₂)

module onlyif {{_ : FUNEXT0}} {i} (wem : WEM i) where
  f : (X : Type i) → X → Bool
  f X x = is-right (wem (Σ X λ x' → x ≠ x'))

  f-natural : dec-natural f
  f-natural X Y e x = go
    where
    y : Y
    y = –> e x
    X-prop : Type i
    X-prop = (Σ X λ x' → x ≠ x')
    Y-prop : Type i
    Y-prop = (Σ Y λ y' → y ≠ y')
    e-lifted : (Σ X λ x' → x ≠ x') ≃ (Σ Y λ y' → y ≠ y')
    e-lifted =
      (Σ X λ x' → x ≠ x') ≃⟨
        Σ-emap e
          (λ y' →
            prop-equiv ¬-is-prop0 ¬-is-prop0
              (contra (λ q → ! (<–-inv-l e x) ∙ (q |in-ctx <– e)))
              (contra (λ q → (q |in-ctx –> e) ∙ <–-inv-r e y'))
          )
        ⟩
      (Σ Y λ y' → y ≠ y') ≃∎
    go : f Y (–> e x) == f X x
    go with wem X-prop | wem Y-prop
    go | inl x₂ | inl x₃ = idp
    go | inr x₂ | inr x₃ = idp
    go | inl x₂ | inr x₃ = ⊥-rec (x₃ (λ yp → x₂ (<– e-lifted yp)))
    go | inr x₂ | inl x₃ = ⊥-rec (x₂ (λ xp → x₃ (–> e-lifted xp)))

  claim-A : f (Lift Unit) (lift unit) == false
  claim-A with wem (Σ (Lift Unit) λ x' → lift unit ≠ x')
  claim-A | inl _ = idp
  claim-A | inr z = ⊥-rec (z (λ {(lift unit , ineq) → ineq idp}))

  claim-B : f (Lift Bool) (lift true) == true
  claim-B with wem (Σ (Lift Bool) λ b' → lift true ≠ b')
  claim-B | inl z = ⊥-rec (z (lift false , lift-≠ Bool-true≠false))
  claim-B | inr _ = idp

  isolated-unit : isolated (lift {j = i} unit)
  isolated-unit (lift unit) = inl idp

  isolated-true : isolated (lift {j = i} true)
  isolated-true (lift true)  = inl idp
  isolated-true (lift false) = inr (lift-≠ Bool-true≠false)

theorem-6-B : {{_ : FUNEXT0}} → ∀ {i} → WEM i →
  Σ ((X : Type i) → X → Bool)
  λ f → dec-natural f ×
  Σ (Type i) λ X → Σ (Type i) λ Y →
  Σ X λ x → Σ Y λ y →
  isolated x × isolated y ×
  (f X x ≠ f Y y)
theorem-6-B wem = f , (f-natural , (Lift Unit , (Lift Bool , (lift unit , (lift true , (isolated-unit , (isolated-true , (λ ineq → Bool-false≠true (! claim-A ∙ ineq ∙ claim-B)))))))))
  where
  open onlyif wem
