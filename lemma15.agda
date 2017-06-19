{-# OPTIONS --without-K --rewriting #-}

module lemma15 where

open import HoTT
open import preliminaries

lemma-15-A : DNE → (P : U) → is-prop P → Σ U λ X → P ⇔ ¬ X
lemma-15-A dne P P-is-prop =
    (¬ P)
  , (¬¬η , dne P P-is-prop)

lemma-15-B : ((P : U) → is-prop P → Σ U λ X → P ⇔ ¬ X) → DNE
lemma-15-B every P P-is-prop = xp ∘ claim-B ∘ claim-A
  where
  X : U
  X = fst (every P P-is-prop)
  px : P → ¬ X
  px = fst (snd (every P P-is-prop))
  xp : ¬ X → P
  xp = snd (snd (every P P-is-prop))
  claim-A : ¬ (¬ P) → ¬ (¬ (¬ X))
  claim-A = ¬-contra (¬-contra px)
  claim-B : ¬ (¬ (¬ X)) → ¬ X
  claim-B = ¬-contra ¬¬η
