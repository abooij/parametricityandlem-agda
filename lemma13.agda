{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma11

module lemma13 where



lemma-13 : {{_ : PROPEXT}} → (f : U → U) → is-inj f → f Unit == Empty → DNE
lemma-13 f f-inj p = lemma-11-B go
  where
  go : (P : U) → is-prop P → Σ U (λ X → P ⇔ ¬ X)
  go P P-is-prop = f P , (to , from)
    where
    to : P → ¬ (f P)
    to =
         prop-Empty-to
       ∘ (λ q → q ∙ p)
       ∘ ap f
       ∘ prop-Unit-from P-is-prop
    from : ¬ (f P) → P
    from =
         prop-Unit-to
       ∘ f-inj P Unit
       ∘ (λ q → q ∙ (! p))
       ∘ prop-Empty-from
