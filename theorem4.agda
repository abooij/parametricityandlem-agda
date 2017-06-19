{-# OPTIONS --without-K --rewriting #-}

module theorem4 where

open import HoTT
open import preliminaries
open import lemma2

complemented : {{_ : PTRUNC}} → ∀ {i} → (P : Type i) → Type (lsucc i)
complemented {i = i} P = Σ (Type i) λ Q → [[ Q ⊔ P ]] × ¬ [[ Q × P ]]

complemented-decidable : {{_ : FUNEXT}} {{_ : PTRUNC}} → ∀ {i} → (P : Type i) → is-prop P → complemented P → P ⊔ ¬ P
complemented-decidable P P-is-prop (Q , total , disjoint) = PTrunc-rec (prop-dec-is-prop P P-is-prop) go total
  where
  go : Q ⊔ P → Coprod P (¬ P)
  go (inl q) = inr (λ p → disjoint p[ q , p ])
  go (inr p) = inl p

theorem-4-A : {{_ : FUNEXT}} {{_ : PTRUNC}} → ∀ {i} → (f : (X : Type i) → X → X) → endomap-natural f → (X : Type i) → (x : X) → f X x ≠ x → LEM i
theorem-4-A {i = i} f f-nat X x ineq P P-is-prop =
  complemented-decidable _ P-is-prop ([[ x == y ]] , (total , disjoint))
  where
  Z : Type i
  Z = Σ X (λ y → [[ [[ x == y ]] ⊔ P ]])
  z : Z
  z = (x , p[ inl p[ idp ] ])
  y : X
  y = fst (f Z z)
  total : [[ [[ x == y ]] ⊔ P ]]
  total = snd (f Z z)
  disjoint : [[ [[ x == y ]] × P ]] → Empty
  disjoint = PTrunc-rec Empty-level (λ {(v , p) → PTrunc-rec Empty-level (claim-C p) v})
    where
    fst-equiv : P → Z ≃ X
    fst-equiv p =
      equiv
        fst
        (λ y → y , p[ inr p ])
        (λ b → idp)
        (λ {(y , w) →
          pair=
            idp
            (prop-has-all-paths PTrunc-level _ _)
        })
    claim-B : P → f Z z ≠ z
    claim-B p q = ineq (
      f X x =⟨ ! (f-nat Z X (fst-equiv p) z) ⟩
      –> (fst-equiv p) (f Z z) =⟨ q |in-ctx –> (fst-equiv p) ⟩
      –> (fst-equiv p) z =⟨ idp ⟩
      x =∎)
    claim-C : P → x ≠ y
    claim-C p q = claim-B p (! repack)
      where
      repack : z == f Z z
      repack =
        pair= q
          (prop-has-all-paths-↓ PTrunc-level)
