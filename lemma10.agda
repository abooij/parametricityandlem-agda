{-# OPTIONS --without-K --rewriting #-}

module lemma10 where

open import HoTT
open import preliminaries

lemma-10-A : LEM → DNE
lemma-10-A lem P P-is-prop negnegP with lem P P-is-prop
lemma-10-A lem P P-is-prop negnegP | inl p = p
lemma-10-A lem P P-is-prop negnegP | inr np = ⊥-rec (negnegP np)

lemma-10-B : {{_ : FUNEXT0}} → DNE → LEM
lemma-10-B dne P P-is-prop = dne (P ⊔ ¬ P) (prop-dec-is-prop0 P P-is-prop) go
  where
  go : ¬ (¬ (P ⊔ ¬ P))
  go n = n (inr (λ p → n (inl p)))
