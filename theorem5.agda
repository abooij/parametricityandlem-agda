{-# OPTIONS --without-K --rewriting #-}

module theorem5 where

open import HoTT
open import preliminaries

theorem-5-A : {{_ : FUNEXT0}} →
  (f : (X : U) → Bool) →
  universe-natural f →
  (X Y : U) →
  f X ≠ f Y → WEM
theorem-5-A f f-nat X Y ineq A = claim-E
  where
  wlog-X : Σ U λ X^ → f X^ == true
  wlog-X with inspect (f X)
  wlog-X | true  with≡ p = X , p
  wlog-X | false with≡ p with inspect (f Y)
  wlog-X | false with≡ p | false with≡ q = ⊥-rec (ineq (p ∙ ! q))
  wlog-X | false with≡ p | true  with≡ q = Y , q
  wlog-Y : Σ U λ Y^ → f Y^ == false
  wlog-Y with inspect (f Y)
  wlog-Y | false with≡ p = Y , p
  wlog-Y | true  with≡ p with inspect (f X)
  wlog-Y | true  with≡ p | true  with≡ q = ⊥-rec (ineq (q ∙ ! p))
  wlog-Y | true  with≡ p | false with≡ q = X , q
  X^ = fst wlog-X
  f-X^ = snd wlog-X
  Y^ = fst wlog-Y
  f-Y^ = snd wlog-Y
  Z : U
  Z = (¬ A × X^) ⊔ (¬ (¬ A) × Y^)
  claim-A : ¬ A → Z ≃ X^
  claim-A negA =
    (¬ A × X^) ⊔ (¬ (¬ A) × Y^)
      ≃⟨ ⊔≃
        (×-emap-l X^ (inhab-prop-equiv-Unit negA ¬-is-prop0))
        (×-emap-l Y^ (inhab-¬-Empty0 negA))
       ⟩
    (Unit × X^) ⊔ (Empty × Y^)
      ≃⟨ ⊔≃
        ×-Unit
        ×-Empty
       ⟩
    X^ ⊔ Empty
      ≃⟨ ⊔-Empty ⟩
    X^
      ≃∎
  claim-B : ¬ A → f Z == true
  claim-B negA = f-nat Z X^ (claim-A negA) ∙ f-X^
  claim-B-contra : f Z == false → ¬ (¬ A)
  claim-B-contra p = λ negA → Bool-true≠false (! (claim-B negA) ∙ p)
  claim-C : A → Z ≃ Y^
  claim-C a =
    (¬ A × X^) ⊔ (¬ (¬ A) × Y^)
      ≃⟨ ⊔≃
        (×-emap-l X^ (inhab-¬-Empty0 a))
        (×-emap-l Y^ (inhab-prop-equiv-Unit (¬¬η a) ¬-is-prop0))
       ⟩
    (Empty × X^) ⊔ (Unit × Y^)
      ≃⟨ ⊔≃
        ×-Empty
        ×-Unit
       ⟩
    Empty ⊔ Y^
      ≃⟨ ⊔-Empty-l ⟩
    Y^
      ≃∎
  claim-D : A → f Z == false
  claim-D a = f-nat Z Y^ (claim-C a) ∙ f-Y^
  claim-D-contra : f Z == true → ¬ A
  claim-D-contra p = λ a → Bool-false≠true (! (claim-D a) ∙ p)
  claim-E : ¬ A ⊔ ¬ (¬ A)
  claim-E with inspect (f Z)
  claim-E | true with≡ x₂ = inl (claim-D-contra x₂)
  claim-E | false with≡ x₂ = inr (claim-B-contra x₂)

-- TODO back direction
