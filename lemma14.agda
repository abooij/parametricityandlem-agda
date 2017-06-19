{-# OPTIONS --without-K --rewriting #-}

module lemma14 where

open import HoTT
open import preliminaries

lemma-14-A : LEM → DNE
lemma-14-A lem P P-is-prop negnegP with lem P P-is-prop
lemma-14-A lem P P-is-prop negnegP | inl p = p
lemma-14-A lem P P-is-prop negnegP | inr np = ⊥-rec (negnegP np)

lemma-14-B : {{_ : FUNEXT0}} → DNE → LEM
lemma-14-B dne P P-is-prop = dne (P ⊔ ¬ P) (prop-dec-is-prop0 P P-is-prop) go
  where
  go : ¬ (¬ (P ⊔ ¬ P))
  go n = n (inr (λ p → n (inl p)))
