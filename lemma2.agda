{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries

module lemma2 where

lemma-2 : {X : U} (x : X) → isolated x ⇔ Σ (Σ U (λ Y → X ≃ Y ⊔ Unit)) (λ {(_ , e) → –> e x == inr unit})
lemma-2 {X} x = to , from
  where
  to : isolated x → Σ (Σ U (λ Y → X ≃ Y ⊔ Unit)) (λ {(_ , e) → –> e x == inr unit})
  to i = (Y , (equiv X-to X-from from-to to-from)) , equiv-compute
    where
    d : X → Bool
    d x' = is-left (i x')
    Y : U
    Y = Σ X (λ x' → d x' == false)
    X-to : X → Y ⊔ Unit
    X-to x' with inspect (i x')
    X-to x' | inl x₁ with≡ _ = inr unit -- x == x'
    X-to x' | inr x₁ with≡ q = inl (x' , ap is-left q) -- x ≠ x'
    X-from : Y ⊔ Unit → X
    X-from (inl (x' , p)) = x'
    X-from (inr unit) = x
    to-from : (x' : X) → X-from (X-to x') == x'
    to-from x' with inspect (i x')
    to-from x' | inl x₁ with≡ _ = x₁ -- x == x'
    to-from x' | inr x₁ with≡ _ = idp -- x ≠ x'
    from-to : (z : Y ⊔ Unit) → X-to (X-from z) == z
    from-to (inl (x' , p)) with inspect (i x')
    from-to (inl (x' , p)) | inl x₁ with≡ x₂ with inr≠inl unit unit (! p ∙ ap is-left x₂)
    from-to (inl (x' , p)) | inl x₁ with≡ x₂ | ()
    from-to (inl (x' , p)) | inr x₁ with≡ x₂ = ap inl (pair= idp (prop-has-all-paths (Bool-level _ _) _ _))
    from-to (inr unit) with inspect (i x)
    from-to (inr unit) | inl x₁ with≡ x₂ = idp
    from-to (inr unit) | inr x₁ with≡ x₂ with x₁ idp
    from-to (inr unit) | inr x₁ with≡ x₂ | ()
    equiv-compute : X-to x == inr unit
    equiv-compute with inspect (i x)
    equiv-compute | inl x₁ with≡ x₂ = idp
    equiv-compute | inr x₁ with≡ x₂ with x₁ idp
    equiv-compute | inr x₁ with≡ x₂ | ()
  from : Σ (Σ U (λ Y → X ≃ Y ⊔ Unit)) (λ {(_ , e) → –> e x == inr unit}) → isolated x
  from ((Y , e) , q) x' with inspect (–> e x')
  from ((Y , e) , q) x' | inl y' with≡ p = inr (λ r → inr≠inl unit y' (! q ∙ ap (–> e) r ∙ p))
  from ((Y , e) , q) x' | inr unit with≡ p = inl (–>-is-inj e x x' (q ∙ ! p))
