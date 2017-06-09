{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import preliminaries
open import lemma2

module theorem3 where

theorem-3-A : (f : (X : U) → X → X) → endomap-natural f → (X : U) → (x : X) → isolated x → f X x ≠ x → LEM
theorem-3-A f nat X x i ineq P P-is-prop = go (inspect (f ((P × Y) ⊔ Unit) (inr unit)))
  where
  Y : U
  Y = fst (fst (fst (lemma-2 x) i))
  g : X ≃ Y ⊔ Unit
  g = snd (fst (fst (lemma-2 x) i))
  go : Singleton (f ((P × Y) ⊔ Unit) (inr unit)) → P ⊔ ¬ P
  go (inl (p , _) with≡ _) = inl p
  go (inr unit with≡ q) = inr not-P
    where
    not-P : ¬ P
    not-P p = inl≠inr (p , f X x , d-claim) unit (
      inl (p , (f X x) , d-claim) =⟨ e-claim-1 ⟩
      –> e (f X x) =⟨ nat _ _ e x ⟩
      f ((P × Y) ⊔ Unit) (–> e x) =⟨ e-claim-2 |in-ctx f ((P × Y) ⊔ Unit) ⟩
      f ((P × Y) ⊔ Unit) (inr unit) =⟨ q ⟩
      inr unit =∎)
      where
      P-contr : is-contr P
      P-contr = inhab-prop-is-contr p P-is-prop
      PY-Y : P × Y ≃ Y
      PY-Y = ×-Unit ∘e ×≃ (contr-equiv-Unit P-contr) (ide Y)
      e : X ≃ (P × Y) ⊔ Unit
      e = (⊔≃ PY-Y (ide Unit)) ⁻¹ ∘e g
      d-claim : is-left (i (f X x)) == false
      d-claim with inspect (i (f X x))
      d-claim | inl x₁ with≡ x₂ with ineq (! x₁)
      d-claim | inl x₁ with≡ x₂ | ()
      d-claim | inr x₁ with≡ x₂ = ap is-left x₂
      e-claim-1 : inl (p , (f X x) , d-claim) == –> e (f X x)
      e-claim-1 with inspect (i (f X x))
      e-claim-1 | inl x₁ with≡ x₂ with ineq (! x₁)
      e-claim-1 | inl x₁ with≡ x₂ | ()
      e-claim-1 | inr x₁ with≡ x₂ = ap inl (pair×= (prop-has-all-paths P-is-prop _ _) idp)
      e-claim-2 : –> e x == inr unit
      e-claim-2 with inspect (i x)
      e-claim-2 | inl x₁ with≡ x₂ = idp
      e-claim-2 | inr x₁ with≡ x₂ with x₁ idp
      e-claim-2 | inr x₁ with≡ x₂ | ()

theorem-3-B : {{_ : FUNEXT}} → LEM →
  Σ ((X : U) → X → X)
    (λ f → endomap-natural f ×
           (Σ U
              (λ X →
                 (Σ X
                    (λ x → f X x ≠ x)))))
theorem-3-B lem = f , (f-natural , Bool , (true , f-bool))
  where
  f-aux : (X : U) → (x : X) → (is-contr (Σ X (λ x' → x' ≠ x))) ⊔ ¬ (is-contr (Σ X (λ x' → x' ≠ x))) → X
  f-aux X x (inl x') = fst (fst x')
  f-aux X x (inr z) = x
  f : (X : U) → X → X
  f X x = f-aux X x (lem (is-contr (Σ X (λ x' → x' ≠ x))) is-contr-is-prop)
  f-natural : endomap-natural f
  f-natural X Y e x with inspect (lem (is-contr (Σ X (λ x' → x' ≠ x))) is-contr-is-prop)
  f-natural X Y e x | inl xc with≡ p =
    –> e (f X x) =⟨ p |in-ctx (λ z → –> e (f-aux X x z)) ⟩
    –> e (fst (fst xc)) =⟨ ! lem-Y |in-ctx f-aux Y (–> e x) ⟩
    f Y (–> e x) =∎
    where
    y : Y
    y = –> e x
    e-lifted : Σ X (λ x' → x' ≠ x) ≃ Σ Y (λ y' → y' ≠ y)
    e-lifted = equiv to from from-to to-from
      where
      to : Σ X (λ x' → x' ≠ x) → Σ Y (λ y' → y' ≠ y)
      to xp = (–> e (fst xp)) , (–>-preserves-≠ e (snd xp))
      from : Σ Y (λ y' → y' ≠ y) → Σ X (λ x' → x' ≠ x)
      from yp =
          <– e (fst yp)
        , transport
          (λ z → (<– e (fst yp) ≠ z))
          (<–-inv-l e x)
          (<–-preserves-≠ e (snd yp))
      to-from : ∀ xp → from (to xp) == xp
      to-from xp = pair= (<–-inv-l e (fst xp)) (prop-has-all-paths-↓ ¬-is-prop)
      from-to : ∀ yp → to (from yp) == yp
      from-to yp = pair= (<–-inv-l (e ⁻¹) (fst yp)) (prop-has-all-paths-↓ ¬-is-prop)
    Y-contr : is-contr (Σ Y (λ y' → y' ≠ y))
    Y-contr = –> (is-contr-equiv e-lifted) xc
    lem-Y : (lem (is-contr (Σ Y (λ y' → y' ≠ y))) is-contr-is-prop) == inl Y-contr
    lem-Y with inspect (lem (is-contr (Σ Y (λ y' → y' ≠ y))) is-contr-is-prop)
    lem-Y | inl x₂ with≡ x₃ = x₃ ∙ ap inl (prop-has-all-paths is-contr-is-prop x₂ Y-contr)
    lem-Y | inr x₂ with≡ x₃ with x₂ Y-contr
    lem-Y | inr x₂ with≡ x₃ | ()
  f-natural X Y e x | inr z  with≡ p =
    –> e (f X x) =⟨ p |in-ctx (λ z → –> e (f-aux X x z)) ⟩
    –> e x =⟨ ! lem-Y |in-ctx f-aux Y (–> e x) ⟩
    f Y (–> e x) =∎
    where
    y : Y
    y = –> e x
    e-lifted : Σ X (λ x' → x' ≠ x) ≃ Σ Y (λ y' → y' ≠ y)
    e-lifted = equiv to from from-to to-from
      where
      to : Σ X (λ x' → x' ≠ x) → Σ Y (λ y' → y' ≠ y)
      to xp = (–> e (fst xp)) , (–>-preserves-≠ e (snd xp))
      from : Σ Y (λ y' → y' ≠ y) → Σ X (λ x' → x' ≠ x)
      from yp =
          <– e (fst yp)
        , transport
          (λ z → (<– e (fst yp) ≠ z))
          (<–-inv-l e x)
          (<–-preserves-≠ e (snd yp))
      to-from : ∀ xp → from (to xp) == xp
      to-from xp = pair= (<–-inv-l e (fst xp)) (prop-has-all-paths-↓ ¬-is-prop)
      from-to : ∀ yp → to (from yp) == yp
      from-to yp = pair= (<–-inv-l (e ⁻¹) (fst yp)) (prop-has-all-paths-↓ ¬-is-prop)
    not-Y-contr : ¬ (is-contr (Σ Y (λ y' → y' ≠ y)))
    not-Y-contr q = z (<– (is-contr-equiv e-lifted) q)
    lem-Y : (lem (is-contr (Σ Y (λ y' → y' ≠ y))) is-contr-is-prop) == inr not-Y-contr
    lem-Y with inspect (lem (is-contr (Σ Y (λ y' → y' ≠ y))) is-contr-is-prop)
    lem-Y | inl x₂ with≡ x₃ with not-Y-contr x₂
    lem-Y | inl x₂ with≡ x₃ | ()
    lem-Y | inr x₂ with≡ x₃ = x₃ ∙ ap inr (prop-has-all-paths ¬-is-prop _ _)
  f-bool : f Bool true ≠ true
  f-bool u = Bool-true≠false (! u ∙ ap (f-aux Bool true) lem-Bool)
    where
    b : Bool
    b = true
    Bool-contr : is-contr (Σ Bool (λ b' → b' ≠ b))
    Bool-contr = (false , Bool-false≠true) , go
      where
      go : (y : Σ Bool (λ b' → b' ≠ b)) → false , Bool-false≠true == y
      go (true  , p) with p idp
      go (true  , p) | ()
      go (false , p) = pair= idp (prop-has-all-paths ¬-is-prop Bool-false≠true p)
    lem-Bool : (lem (is-contr (Σ Bool (λ b' → b' ≠ b))) is-contr-is-prop) == inl Bool-contr
    lem-Bool with inspect (lem (is-contr (Σ Bool (λ b' → b' ≠ b))) is-contr-is-prop)
    lem-Bool | inl x₁ with≡ x₂ = x₂ ∙ ap inl (prop-has-all-paths is-contr-is-prop _ _)
    lem-Bool | inr x₁ with≡ x₂ with x₁ Bool-contr
    lem-Bool | inr x₁ with≡ x₂ | ()
