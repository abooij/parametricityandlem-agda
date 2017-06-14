{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma15

module theorem16 where

theorem-16 : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}} {{_ : FUNEXT0}} {{_ : FUNEXT}} →
  (e : U ≃ U) →
  (A : U) → [[ A ]] →
  –> e A == Empty →
  LEM
theorem-16 e A pa eq = lemma-15 (–> e) (–>-is-inj e) A pa eq
