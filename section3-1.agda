{-# OPTIONS --without-K --rewriting #-}

module section3-1 where

open import HoTT
open import preliminaries
open import lemma10

section3-1 : {{_ : FUNEXT}} {{_ : PROPEXT}} →
  LEM →
  Σ (U ≃ U) λ e → –> e Empty == Unit
section3-1 lem = equiv f f f-inv f-inv , f-comp
  where
  ¬¬-id : (X : U) → is-prop X → ¬ (¬ X) == X
  ¬¬-id X X-is-prop = ua-prop ¬-is-prop X-is-prop (lemma-10-A lem X X-is-prop) ¬¬η
  f : U → U
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
  f-comp : f Empty == Unit
  f-comp with lem (is-prop Empty) is-prop-is-prop
  f-comp | inl Empty-is-prop = ua-prop ¬-is-prop (raise-level _ Unit-level) (cst unit) (cst (idf _))
  f-comp | inr Empty-no-prop = ⊥-rec (Empty-no-prop Empty-level)
