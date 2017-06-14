{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma11

module theorem12 where

theorem-12 : {{_ : PROPEXT}} → (f : U → U) → is-inj f → f Unit == Empty → DNE
theorem-12 f f-inj p = lemma-11-B go
  where
  go : (P : U) → is-prop P → Σ U (λ X → P ⇔ ¬ X)
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
       ∘ f-inj P Unit             -- f left-cancellable
       ∘ (λ q → q ∙ (! p))        -- assumption f Unit == Empty
       ∘ prop-Empty-from          -- propext
