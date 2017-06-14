{-# OPTIONS --without-K --rewriting #-}

module lemma14 where

open import HoTT
open import preliminaries

lemma-14 : {{_ : UA}} {{_ : FUNEXT}} {{_ : PTRUNC}} (A : U) → [[ A ]] → (P : U) → is-prop P → P ⇔ (P × A == A)
lemma-14 A pa P P-is-prop = to , from
  where
  to : P → P × A == A
  to p = ua (
    P × A
      ≃⟨ ×-emap-l A (inhab-prop-equiv-Unit p P-is-prop) ⟩
    Unit × A
      ≃⟨ ×-Unit ⟩
    A
      ≃∎)
  from : P × A == A → P
  from q = coe (! claim-D) unit
    where
    claim-A : [[ P × A ]] == [[ A ]]
    claim-A = ap [[_]] q
    claim-B : [[ P × A ]] == Unit
    claim-B = claim-A ∙ ua (inhab-prop-equiv-Unit pa PTrunc-level)
    claim-C : [[ P ]] × [[ A ]] == Unit
    claim-C = ! (ua [[]]×) ∙ claim-B
    claim-D : P == Unit
    claim-D = ua (
      P
        ≃⟨ ([[]]prop P-is-prop) ⁻¹ ⟩
      [[ P ]]
        ≃⟨ ×-Unit-r ⁻¹ ⟩
      [[ P ]] × Unit
        ≃⟨ ×-emap-r [[ P ]] ((inhab-prop-equiv-Unit pa PTrunc-level) ⁻¹) ⟩
      [[ P ]] × [[ A ]]
        ≃∎
      ) ∙ claim-C
