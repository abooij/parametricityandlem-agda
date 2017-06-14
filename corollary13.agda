{-# OPTIONS --without-K --rewriting #-}

module corollary13 where

open import HoTT
open import preliminaries
open import theorem12

corollary-13 : {{_ : PROPEXT}} → (aut : U ≃ U) → –> aut Unit == Empty → DNE
corollary-13 aut aut-Unit = theorem-12 (–> aut) (–>-is-inj aut) aut-Unit
