{-# OPTIONS --without-K --rewriting #-}

module theorem10 where

open import HoTT
open import preliminaries
open import lemma14

theorem-10 : {{_ : FUNEXT}} {{_ : PROPEXT}} →  ∀ {i} →
  LEM i →
  Σ (Type i ≃ Type i) λ e → –> e (Lift Empty) == Lift Unit
theorem-10 {i = i} lem = equiv f f f-inv f-inv , f-comp
  where
  ¬¬-id : (X : Type i) → is-prop X → ¬ (¬ X) == X
  ¬¬-id X X-is-prop = ua-prop ¬-is-prop X-is-prop (lemma-14-A lem X X-is-prop) ¬¬η
  f : Type i → Type i
  f X with lem (is-prop X) is-prop-is-prop
  f X | inl X-is-prop = ¬ X
  f X | inr X-no-prop = X
  f-inv : ∀ X → f (f X) == X
  f-inv X with lem (is-prop X) is-prop-is-prop
  f-inv X | inl X-is-prop with lem (is-prop (¬ X)) is-prop-is-prop
  f-inv X | inl X-is-prop | inl negX-is-prop = ¬¬-id X X-is-prop
  f-inv X | inl X-is-prop | inr negX-no-prop = ⊥-rec (negX-no-prop ¬-is-prop)
  f-inv X | inr X-no-prop with lem (is-prop X) is-prop-is-prop
  f-inv X | inr X-no-prop | inl X-is-prop' = ⊥-rec (X-no-prop X-is-prop')
  f-inv X | inr X-no-prop | inr X-no-prop' = idp
  f-comp : f (Lift Empty) == Lift Unit
  f-comp with lem (is-prop (Lift Empty)) is-prop-is-prop
  f-comp | inl Empty-is-prop =
    ua-prop
      ¬-is-prop
      ((Lift-level (raise-level _ Unit-level)))
      (cst (lift unit))
      (cst lower)
  f-comp | inr Empty-no-prop = ⊥-rec (Empty-no-prop (Lift-level Empty-level))
