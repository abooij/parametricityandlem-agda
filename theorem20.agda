{-# OPTIONS --without-K --rewriting #-}

module theorem20 where

open import HoTT
open import preliminaries
open import lemma19

theorem-20 : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}}
  {{_ : FUNEXT0}} {{_ : FUNEXT}} → ∀ {i} →
  (e : Type i ≃ Type i) →
  (A : Type i) → [[ A ]] →
  –> e A == Lift Empty →
  LEM i
theorem-20 e A pa eq = lemma-19 (–> e) (–>-is-inj e) A pa eq
