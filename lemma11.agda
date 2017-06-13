{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries

module lemma11 where

lemma-11-A : DNE → (P : U) → is-prop P → Σ U λ X → P ⇔ ¬ X
lemma-11-A dne P P-is-prop =
    (¬ P)
  , (¬¬η , dne P P-is-prop)

lemma-11-B : ((P : U) → is-prop P → Σ U λ X → P ⇔ ¬ X) → DNE
lemma-11-B every P P-is-prop = xp ∘ claim-B ∘ claim-A
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
