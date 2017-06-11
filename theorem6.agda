{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma2

module theorem6 where

theorem-6-A : {{_ : FUNEXT0}} → (f : (X : U) → X → Bool) → dec-natural f → (X Y : U) → (x : X) → isolated x → (y : Y) → isolated y → f X x ≠ f Y y → WEM
theorem-6-A f f-nat X Y x x-isol y y-isol ineq A = claim-E
  where
  wlog-X : Σ U λ X' → Σ X' λ x' → isolated x' × (f X' x' == true)
  wlog-X with inspect (f X x)
  wlog-X | true  with≡ p = X , (x , (x-isol , p))
  wlog-X | false with≡ p with inspect (f Y y)
  wlog-X | false with≡ p | false with≡ q with ineq (p ∙ ! q)
  wlog-X | false with≡ p | false with≡ q | ()
  wlog-X | false with≡ p | true  with≡ q = Y , (y , (y-isol , q))
  wlog-Y : Σ U λ Y' → Σ Y' λ y' → isolated y' × (f Y' y' == false)
  wlog-Y with inspect (f Y y)
  wlog-Y | false with≡ p = Y , (y , (y-isol , p))
  wlog-Y | true  with≡ p with inspect (f X x)
  wlog-Y | true  with≡ p | true  with≡ q with ineq (q ∙ ! p)
  wlog-Y | true  with≡ p | true  with≡ q | ()
  wlog-Y | true  with≡ p | false with≡ q = X , (x , (x-isol , q))
  X^ : U
  X^ = fst wlog-X
  x^ : X^
  x^ = fst (snd wlog-X)
  x^-isol : isolated x^
  x^-isol = fst (snd (snd wlog-X))
  f-x^ : f X^ x^ == true
  f-x^ = snd (snd (snd wlog-X))
  Y^ : U
  Y^ = fst wlog-Y
  y^ : Y^
  y^ = fst (snd wlog-Y)
  y^-isol : isolated y^
  y^-isol = fst (snd (snd wlog-Y))
  f-y^ : f Y^ y^ == false
  f-y^ = snd (snd (snd wlog-Y))
  X' : U
  X' = fst (fst (fst (lemma-2 x^) x^-isol))
  X'-e : X^ ≃ X' ⊔ Unit
  X'-e = snd (fst (fst (lemma-2 x^) x^-isol))
  Y' : U
  Y' = fst (fst (fst (lemma-2 y^) y^-isol))
  Y'-e : Y^ ≃ Y' ⊔ Unit
  Y'-e = snd (fst (fst (lemma-2 y^) y^-isol))
  Z : U
  Z = (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y'))
  z : Z
  z = (inl unit) , (inl unit)
  claim-A : ¬ A → Z ≃ X^
  claim-A negA =
    (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y')) ≃⟨
      ×≃
        (⊔≃ (ide Unit) (×≃ (contr-equiv-Unit (inhab-prop-is-contr negA ¬-is-prop0) ) (ide _)))
        (⊔≃ (ide Unit) (×≃ (inhab-¬-Empty negA) (ide _)))
      ⟩
    (Unit ⊔ (Unit × X')) × (Unit ⊔ (Empty × Y')) ≃⟨
      ×≃ (⊔≃ (ide Unit) ×-Unit) (⊔≃ (ide Unit) ×-Empty) ⟩
    (Unit ⊔ X') × (Unit ⊔ Empty) ≃⟨ ×≃ (X'-e ⁻¹ ∘e ⊔-comm) ⊔-Empty ⟩
    X^ × Unit ≃⟨ ×-Unit-r ⟩
    X^ ≃∎
  claim-B : ¬ A → f Z z == true
  claim-B negA = ! (f-nat Z X^ (claim-A negA) z) ∙ f-x^
  claim-C : A → Z ≃ Y^
  claim-C a =
    (Unit ⊔ (¬ A × X')) × (Unit ⊔ (¬ (¬ A) × Y')) ≃⟨
      ×≃
        (⊔≃ (ide Unit) (×≃ (inhab-¬-Empty a) (ide X')))
        (⊔≃ (ide Unit) (×≃ (contr-equiv-Unit (inhab-prop-is-contr (λ x₁ → x₁ a) ¬-is-prop0)) (ide Y')))
      ⟩
    (Unit ⊔ (Empty × X')) × (Unit ⊔ (Unit × Y')) ≃⟨
      ×≃ (⊔≃ (ide Unit) ×-Empty) (⊔≃ (ide Unit) ×-Unit) ⟩
    (Unit ⊔ Empty) × (Unit ⊔ Y') ≃⟨
      ×≃ ⊔-Empty (Y'-e ⁻¹ ∘e ⊔-comm) ⟩
    Unit × Y^ ≃⟨ ×-Unit ⟩
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
