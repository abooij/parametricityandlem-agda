{-# OPTIONS --without-K --rewriting #-}

module theorem8 where

open import HoTT
open import preliminaries

theorem-8 : {{_ : PTRUNC}} {{_ : FUNEXT0}} → ∀ {i} →
  (P Q : Type i → Type i) → equiv-invariant P → equiv-invariant Q →
  ((Z : Type i) → [[ P Z ⊔ Q Z ]]) →
  (X Y : Type i) → ¬ (P X) → ¬ (Q Y) →
  WEM i
theorem-8 {i = i}P Q P-inv Q-inv total X Y negPX negQY A = claim-E
  where
  Z : Type i
  Z = (¬ A × X) ⊔ ¬ (¬ A) × Y
  claim-A : A → Z ≃ Y
  claim-A a =
    (¬ A × X) ⊔ (¬ (¬ A) × Y)
      ≃⟨ ⊔≃
        (×≃ (inhab-¬-Empty0 a) (ide X))
        (×≃
          (inhab-prop-equiv-Unit (¬¬η a) ¬-is-prop0)
          (ide Y)
        )
       ⟩
    (Empty × X) ⊔ (Unit × Y)
      ≃⟨ ⊔≃ ×-Empty ×-Unit ⟩
    Empty ⊔ Y
      ≃⟨ ⊔-Empty-l ⟩
    Y
      ≃∎
  claim-B : A → ¬ (Q Z)
  claim-B a = λ qz → negQY (–> (Q-inv (claim-A a)) qz)
  claim-B-contra : Q Z → ¬ A
  claim-B-contra = λ qz a → claim-B a qz
  claim-C : ¬ A → Z ≃ X
  claim-C negA =
    (¬ A × X) ⊔ (¬ (¬ A) × Y)
      ≃⟨ ⊔≃
        (×≃
          (inhab-prop-equiv-Unit negA ¬-is-prop0)
          (ide X)
        )
        (×≃
          (inhab-¬-Empty0 negA)
          (ide Y)
        )
       ⟩
    (Unit × X) ⊔ (Empty × Y)
      ≃⟨ ⊔≃ ×-Unit ×-Empty ⟩
    X ⊔ Empty
      ≃⟨ ⊔-Empty ⟩
    X
      ≃∎
  claim-D : ¬ A → ¬ (P Z)
  claim-D negA = λ pz → negPX (–> (P-inv (claim-C negA)) pz)
  claim-D-contra : P Z → ¬ (¬ A)
  claim-D-contra = λ pz negA → claim-D negA pz
  claim-E : ¬ A ⊔ ¬ (¬ A)
  claim-E = PTrunc-rec (prop-dec-is-prop0 (¬ A) ¬-is-prop0) go (total Z)
    where
    go : P Z ⊔ Q Z → (¬ A) ⊔ (¬ (¬ A))
    go (inl pz) = inr (claim-D-contra pz)
    go (inr qz) = inl (claim-B-contra qz)
