{-# OPTIONS --without-K --rewriting #-}

module theorem9 where

open import HoTT
open import preliminaries

theorem-9 : {{_ : PUSHOUT}} {{_ : PTRUNC}} {{_ : FUNEXT0}} →
  (P Q : (X : U) → X → U) →
  pointed-invariant P → pointed-invariant Q →
  ((Z : U) → (z : Z) → [[ P Z z ⊔ Q Z z ]]) →
  (X Y : U) → (x : X) → (y : Y) →
  ¬ (P X x) → ¬ (Q Y y) →
  WEM
theorem-9 P Q P-inv Q-inv total X Y x y negPXx negQYy A = claim-E
  where
  Z : U
  Z = (Σ X λ x' → (x == x') * ¬ A) × (Σ Y λ y' → (y == y') * ¬ (¬ A))
  z : Z
  z = (x , (jleft idp)) , (y , jleft idp)
  claim-A : A → Z ≃ Y
  claim-A a =
    (Σ X λ x' → (x == x') * ¬ A) × (Σ Y λ y' → (y == y') * ¬ (¬ A))
      ≃⟨ ×-emap
        (Σ-emap-r (λ x' → *-emap (ide _) (inhab-¬-Empty0 a)))
        (Σ-emap-r (λ y' → *-emap (ide _) (inhab-prop-equiv-Unit (λ negA → negA a) ¬-is-prop0)))
       ⟩
    (Σ X λ x' → (x == x') * Empty) × (Σ Y λ y' → (y == y') * Unit)
      ≃⟨ ×-emap
        (Σ-emap-r (λ x' → join-Empty-idem))
        (Σ-emap-r (λ y' → join-Unit-idem))
       ⟩
    (Σ X λ x' → (x == x')) × (Σ Y λ y' → Unit)
      ≃⟨ ×-emap
        (singleton-equiv-Unit x)
        Σ₂-Unit
       ⟩
    Unit × Y
      ≃⟨ ×-Unit ⟩
    Y
      ≃∎
  claim-B : A → ¬ (Q Z z)
  claim-B a = λ qz → negQYy (–> (Q-inv (claim-A a) z) qz)
  claim-B-contra : Q Z z → ¬ A
  claim-B-contra = λ qz a → claim-B a qz
  claim-C : ¬ A → Z ≃ X
  claim-C negA =
    (Σ X λ x' → (x == x') * ¬ A) × (Σ Y λ y' → (y == y') * ¬ (¬ A))
      ≃⟨ ×-emap
        (Σ-emap-r (λ y' → *-emap (ide _) (inhab-prop-equiv-Unit negA ¬-is-prop0)))
        (Σ-emap-r (λ x' → *-emap (ide _) (inhab-¬-Empty0 negA)))
       ⟩
    (Σ X λ x' → (x == x') * Unit) × (Σ Y λ y' → (y == y') * Empty)
      ≃⟨ ×-emap
        (Σ-emap-r (λ x' → join-Unit-idem))
        (Σ-emap-r (λ y' → join-Empty-idem))
       ⟩
    (Σ X λ x' → Unit) × (Σ Y λ y' → (y == y'))
      ≃⟨ ×-emap
        Σ₂-Unit
        (singleton-equiv-Unit y)
       ⟩
    X × Unit
      ≃⟨ ×-Unit-r ⟩
    X
    ≃∎
  claim-D : ¬ A → ¬ (P Z z)
  claim-D negA = λ pz → negPXx (–> (P-inv (claim-C negA) z) pz)
  claim-D-contra : P Z z → ¬ (¬ A)
  claim-D-contra pz = λ negA → claim-D negA pz
  claim-E : ¬ A ⊔ ¬ (¬ A)
  claim-E = PTrunc-rec (prop-dec-is-prop0 (¬ A) ¬-is-prop0) go (total Z z)
    where
    go : P Z z ⊔ Q Z z → (¬ A) ⊔ (¬ (¬ A))
    go (inl pz) = inr (claim-D-contra pz)
    go (inr qz) = inl (claim-B-contra qz)
