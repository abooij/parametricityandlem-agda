{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma2
open import theorem6

module theorem7 where

theorem-7-A : {{_ : PTRUNC}} {{_ : FUNEXT}} →
  (f : (X : U) → X → Bool) →
  dec-natural f →
  (X Y : U) →
  (x : X) → is-prop (x == x) →
  (y : Y) → is-prop (y == y) →
  f X x ≠ f Y y → WEM
theorem-7-A f f-nat X Y x x-prop y y-prop ineq A = claim-E
  where
  wlog-X : Σ U λ X' → Σ X' λ x' → is-prop (x' == x') × (f X' x' == true)
  wlog-X with inspect (f X x)
  wlog-X | true  with≡ p = X , (x , (x-prop , p))
  wlog-X | false with≡ p with inspect (f Y y)
  wlog-X | false with≡ p | false with≡ q with ineq (p ∙ ! q)
  wlog-X | false with≡ p | false with≡ q | ()
  wlog-X | false with≡ p | true  with≡ q = Y , (y , (y-prop , q))
  wlog-Y : Σ U λ Y' → Σ Y' λ y' → is-prop (y' == y') × (f Y' y' == false)
  wlog-Y with inspect (f Y y)
  wlog-Y | false with≡ p = Y , (y , (y-prop , p))
  wlog-Y | true  with≡ p with inspect (f X x)
  wlog-Y | true  with≡ p | true  with≡ q with ineq (q ∙ ! p)
  wlog-Y | true  with≡ p | true  with≡ q | ()
  wlog-Y | true  with≡ p | false with≡ q = X , (x , (x-prop , q))
  X^ : U
  X^ = fst wlog-X
  x^ : X^
  x^ = fst (snd wlog-X)
  x^-prop : is-prop (x^ == x^)
  x^-prop = fst (snd (snd wlog-X))
  f-x^ : f X^ x^ == true
  f-x^ = snd (snd (snd wlog-X))
  Y^ : U
  Y^ = fst wlog-Y
  y^ : Y^
  y^ = fst (snd wlog-Y)
  y^-prop : is-prop (y^ == y^)
  y^-prop = fst (snd (snd wlog-Y))
  f-y^ : f Y^ y^ == false
  f-y^ = snd (snd (snd wlog-Y))
  Z : U
  Z = (Σ X^ λ x' → [[ [[ x^ == x' ]] ⊔ ¬ A ]]) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ⊔ ¬ (¬ A) ]])
  z : Z
  z = (x^ , p[ inl p[ idp ] ]) , (y^ , p[ inl p[ idp ] ])
  claim-A : ¬ A → Z ≃ X^
  claim-A negA =
    (Σ X^ λ x' → [[ [[ x^ == x' ]] ⊔ ¬ A ]]) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ⊔ ¬ (¬ A) ]])
      ≃⟨ ×≃
        (Σ-emap-r (λ x' → [[]]≃ (⊔≃ (ide _) (inhab-prop-equiv-Unit negA ¬-is-prop)) ))
        (Σ-emap-r (λ y' → [[]]≃ (⊔≃ (ide _) (inhab-¬-Empty negA))))
       ⟩
    (Σ X^ λ x' → [[ [[ x^ == x' ]] ⊔ Unit ]]) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ⊔ Empty ]])
      ≃⟨ ×≃
        (Σ-emap-r (λ x' →
          prop-equiv PTrunc-level (raise-level -2 Unit-level)
            (λ _ → unit)
            (λ _ → p[ inr unit ])
          )
        )
        (Σ-emap-r (λ y' → [[]]≃ ⊔-Empty))
       ⟩
    (Σ X^ λ x' → Unit) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ]])
      ≃⟨ ×≃
        Σ₂-Unit
        (Σ-emap-r (λ y' → [[]]μ))
       ⟩
    X^ × (Σ Y^ λ y' → [[ y^ == y' ]])
      ≃⟨ ×≃
        (ide X^)
        (contr-equiv-Unit (component-is-prop y^ y^-prop))
       ⟩
    X^ × Unit
      ≃⟨ ×-Unit-r ⟩
    X^
      ≃∎
  claim-C : A → Z ≃ Y^
  claim-C a =
    (Σ X^ λ x' → [[ [[ x^ == x' ]] ⊔ ¬ A ]]) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ⊔ ¬ (¬ A) ]])
      ≃⟨ ×≃
        (Σ-emap-r (λ x' → [[]]≃ (⊔≃ (ide _) (inhab-¬-Empty a))))
        (Σ-emap-r (λ y' → [[]]≃ (⊔≃ (ide _) (inhab-prop-equiv-Unit (λ x₁ → x₁ a) ¬-is-prop))))
       ⟩
    (Σ X^ λ x' → [[ [[ x^ == x' ]] ⊔ Empty ]]) × (Σ Y^ λ y' → [[ [[ y^ == y' ]] ⊔ Unit ]])
      ≃⟨ ×≃
        (Σ-emap-r (λ x' → [[]]≃ ⊔-Empty))
        (Σ-emap-r (λ y' →
          prop-equiv PTrunc-level (raise-level -2 Unit-level)
            (λ _ → unit)
            (λ _ → p[ inr unit ])
          )
        )
       ⟩
    (Σ X^ λ x' → [[ [[ x^ == x' ]] ]]) × (Σ Y^ λ y' → Unit)
      ≃⟨ ×≃
        (Σ-emap-r (λ x' → [[]]μ))
        Σ₂-Unit
       ⟩
    (Σ X^ λ x' → [[ x^ == x' ]]) × Y^
      ≃⟨ ×≃
        (contr-equiv-Unit (component-is-prop x^ x^-prop))
        (ide Y^)
       ⟩
    Unit × Y^
      ≃⟨ ×-Unit ⟩
    Y^
      ≃∎
  claim-B : ¬ A → f Z z == true
  claim-B negA = ! (f-nat Z X^ (claim-A negA) z) ∙ f-x^
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

theorem-7-B : {{_ : PTRUNC}} {{_ : FUNEXT0}} → WEM →
  Σ ((X : U) → X → Bool)
  λ f → dec-natural f ×
  Σ U λ X → Σ U λ Y →
  Σ X λ x → Σ Y λ y →
  is-prop (x == x) × is-prop (y == y) ×
  (f X x ≠ f Y y)
theorem-7-B wem = f , (f-natural , (Unit , (Bool , (unit , (true , (raise-level _ (raise-level _ Unit-level) _ _ , (Bool-level true true , (λ ineq → Bool-false≠true (! claim-A ∙ ineq ∙ claim-B)))))))))
  where
  open onlyif wem
