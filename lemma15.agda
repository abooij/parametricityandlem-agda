{-# OPTIONS --without-K --rewriting #-}

module lemma15 where

open import HoTT
open import preliminaries

lemma-15-A : ∀ {i} → DNE i → (P : Type i) → is-prop P → Σ (Type i) λ X → P ⇔ ¬ X
lemma-15-A dne P P-is-prop =
    (¬ P)
  , (¬¬η , dne P P-is-prop)

lemma-15-B : ∀ {i} → ((P : Type i) → is-prop P → Σ (Type i) λ X → P ⇔ ¬ X) → DNE i
lemma-15-B {i = i} every P P-is-prop = xp ∘ claim-B ∘ claim-A
  where
  X : Type i
  X = fst (every P P-is-prop)
  px : P → ¬ X
  px = fst (snd (every P P-is-prop))
  xp : ¬ X → P
  xp = snd (snd (every P P-is-prop))
  claim-A : ¬ (¬ P) → ¬ (¬ (¬ X))
  claim-A = ¬-contra (¬-contra px)
  claim-B : ¬ (¬ (¬ X)) → ¬ X
  claim-B = ¬-contra ¬¬η
