{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma13

module theorem12 where

theorem-12 : {{_ : PROPEXT}} → (aut : U ≃ U) → –> aut Unit == Empty → DNE
theorem-12 aut aut-Unit = lemma-13 (–> aut) (–>-is-inj aut) aut-Unit
