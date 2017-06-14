{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma10
open import lemma11
open import lemma14

module lemma15 where

lemma-15 : {{_ : UA}} {{_ : PROPEXT}} {{_ : PTRUNC}} {{_ : FUNEXT0}} {{_ : FUNEXT}} → (f : U → U) → is-inj f → (A : U) → [[ A ]] → f A == Empty → LEM
lemma-15 f f-inj A pa eq = lemma-10-B (lemma-11-B go)
  where
  go : (P : U) → is-prop P → Σ U (λ X → P ⇔ ¬ X)
  go P P-is-prop = (f (P × A)) , (to , from)
    where
    to : P → ¬ (f (P × A))
    to =
        prop-Empty-to                   -- propext
      ∘ (λ q → q ∙ eq)                  -- assumption f A == Empty
      ∘ ap f                            --
      ∘ fst (lemma-14 A pa P P-is-prop) -- lemma 14
    from : ¬ (f (P × A)) → P
    from =
        snd (lemma-14 A pa P P-is-prop) -- lemma 14
      ∘ f-inj _ _                       -- f left-cancellable
      ∘ (λ q → q ∙ (! eq))              -- assumption f A == Empty
      ∘ prop-Empty-from                 -- propext
