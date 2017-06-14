{-# OPTIONS --without-K --rewriting #-}

module corollary17 where

open import HoTT
open import preliminaries
open import theorem16

corollary-17 : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}} {{_ : FUNEXT0}} {{_ : FUNEXT}} →
  (g : U ≃ U) →
  (–> g Empty ≠ Empty) →
  ¬ (¬ LEM)
corollary-17 g ineq = ¬-contra (¬-contra claim-B) claim-C
  where
  f : U ≃ U
  f = g ⁻¹
  claim-A : –> g Empty → [[ –> g Empty ]]
  claim-A = p[_]
  claim-B : –> g Empty → LEM
  claim-B ge = theorem-16 f (–> g Empty) (claim-A ge) (<–-inv-l g Empty)
  claim-C : ¬ (¬ (–> g Empty))
  claim-C = ¬-contra prop-Empty-from ineq
