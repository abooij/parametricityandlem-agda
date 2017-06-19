{-# OPTIONS --without-K --rewriting #-}

module corollary17 where

open import HoTT
open import preliminaries
open import theorem16

corollary-17 : {{_ : PROPEXT}} → (aut : U ≃ U) → –> aut Unit == Empty → DNE
corollary-17 aut aut-Unit = theorem-16 (–> aut) (–>-is-inj aut) aut-Unit
