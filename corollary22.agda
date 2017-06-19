{-# OPTIONS --without-K --rewriting #-}

module corollary22 where

open import HoTT
open import preliminaries
open import corollary21

corollary-22-A : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}}
  {{_ : FUNEXT0}} {{_ : FUNEXT}} → ∀ {i} →
  (g : Type (lsucc i) ≃ Type (lsucc i)) →
  (–> g (LEM i) ≠ LEM i) →
  ¬ (¬ (LEM i))
corollary-22-A {i = i} g ineq notlem = claim-D notlem
  where
  claim-A : LEM i == Lift Empty
  claim-A = ua (prop-equiv LEM-is-prop (Lift-level Empty-level) (lift ∘ notlem) (⊥-rec ∘ lower))
  claim-B : ¬ (¬ (LEM (lsucc i)))
  claim-B = corollary-21 g (transport (λ X → –> g X ≠ X) claim-A ineq)
  claim-C : LEM (lsucc i) → LEM i
  claim-C lemSi P P-is-prop = lowerPchoice
    where
    Pchoice : (Lift P) ⊔ ¬ (Lift P)
    Pchoice = lemSi (Lift P) (Lift-level P-is-prop)
    lowerPchoice : P ⊔ ¬ P
    lowerPchoice with Pchoice
    lowerPchoice | inl (lift p) = inl p
    lowerPchoice | inr np = inr (np ∘ lift)
  claim-D : ¬ (¬ (LEM i))
  claim-D = ¬-contra (¬-contra claim-C) claim-B
