{-# OPTIONS --without-K --rewriting #-}

module theorem16 where

open import HoTT
open import preliminaries
open import lemma15

theorem-16 : {{_ : PROPEXT}} → ∀ {i} → (f : Type i → Type i) → is-inj f → f (Lift Unit) == (Lift Empty) → DNE i
theorem-16 {i = i} f f-inj p = lemma-15-B go
  where
  go : (P : Type i) → is-prop P → Σ (Type i) (λ X → P ⇔ ¬ X)
  go P P-is-prop = f P , (to , from)
    where
    to : P → ¬ (f P)
    to =
         prop-Empty-to            -- propext
       ∘ (λ q → q ∙ p)            -- assumption f Unit == Empty
       ∘ ap f                     --
       ∘ prop-Unit-from P-is-prop -- propext
    from : ¬ (f P) → P
    from =
         prop-Unit-to             -- propext
       ∘ f-inj P (Lift Unit)             -- f left-cancellable
       ∘ (λ q → q ∙ (! p))        -- assumption f Unit == Empty
       ∘ prop-Empty-from          -- propext
