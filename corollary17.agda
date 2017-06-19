{-# OPTIONS --without-K --rewriting #-}

module corollary17 where

open import HoTT
open import preliminaries
open import theorem16

corollary-17 : {{_ : PROPEXT}} → ∀ {i} → (aut : Type i ≃ Type i) → –> aut (Lift Unit) == (Lift Empty) → DNE i
corollary-17 aut aut-Unit = theorem-16 (–> aut) (–>-is-inj aut) aut-Unit
