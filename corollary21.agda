{-# OPTIONS --without-K --rewriting #-}

module corollary21 where

open import HoTT
open import preliminaries
open import theorem20

corollary-21 : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}}
  {{_ : FUNEXT0}} {{_ : FUNEXT}} → ∀ {i} →
  (g : Type i ≃ Type i) →
  (–> g (Lift Empty) ≠ (Lift Empty)) →
  ¬ (¬ (LEM i))
corollary-21 {i = i} g ineq = ¬-contra (¬-contra claim-B) claim-C
  where
  f : Type i ≃ Type i
  f = g ⁻¹
  claim-A : –> g (Lift Empty) → [[ –> g (Lift Empty) ]]
  claim-A = p[_]
  claim-B : –> g (Lift Empty) → LEM i
  claim-B ge = theorem-20 f (–> g (Lift Empty)) (claim-A ge) (<–-inv-l g (Lift Empty))
  claim-C : ¬ (¬ (–> g (Lift Empty)))
  claim-C = ¬-contra prop-Empty-from ineq
