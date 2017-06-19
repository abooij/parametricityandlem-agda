{-# OPTIONS --without-K --rewriting #-}

module theorem3 where

open import HoTT
open import preliminaries
open import lemma2

theorem-3-A : ∀ {i} → (f : (X : Type i) → X → X) → endomap-natural f → (X : Type i) → (x : X) → isolated x → f X x ≠ x → LEM i
theorem-3-A {i = i} f nat X x j ineq P P-is-prop = go (inspect (f ((P × Y) ⊔ Unit) (inr unit)))
  where
  Y : Type i
  Y = fst (fst (fst (lemma-2 x) j))
  g : X ≃ Y ⊔ Unit
  g = snd (fst (fst (lemma-2 x) j))
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
      d-claim : is-left (j (f X x)) == false
      d-claim with inspect (j (f X x))
      d-claim | inl x₁ with≡ x₂ = ⊥-rec (ineq (! x₁))
      d-claim | inr x₁ with≡ x₂ = ap is-left x₂
      e-claim-1 : inl (p , (f X x) , d-claim) == –> e (f X x)
      e-claim-1 with inspect (j (f X x))
      e-claim-1 | inl x₁ with≡ x₂ = ⊥-rec (ineq (! x₁))
      e-claim-1 | inr x₁ with≡ x₂ = ap inl (pair×= (prop-has-all-paths P-is-prop _ _) idp)
      e-claim-2 : –> e x == inr unit
      e-claim-2 with inspect (j x)
      e-claim-2 | inl x₁ with≡ x₂ = idp
      e-claim-2 | inr x₁ with≡ x₂ = ⊥-rec (x₁ idp)

theorem-3-B : {{_ : FUNEXT}} → ∀ {i} → LEM i →
  Σ ((X : Type i) → X → X)
    (λ f → endomap-natural f ×
           (Σ (Type i)
              (λ X →
                 (Σ X
                    (λ x → f X x ≠ x)))))
theorem-3-B {i = i} lem = f , (f-natural , Lift Bool , (lift true , f-bool))
  where
  f-aux : (X : Type i) → (x : X) → (is-contr (Σ X (λ x' → x' ≠ x))) ⊔ ¬ (is-contr (Σ X (λ x' → x' ≠ x))) → X
  f-aux X x (inl x') = fst (fst x')
  f-aux X x (inr z) = x
  f : (X : Type i) → X → X
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
    lem-Y | inr x₂ with≡ x₃ = ⊥-rec (x₂ Y-contr)
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
    lem-Y | inl x₂ with≡ x₃ = ⊥-rec (not-Y-contr x₂)
    lem-Y | inr x₂ with≡ x₃ = x₃ ∙ ap inr (prop-has-all-paths ¬-is-prop _ _)
  f-bool : f (Lift Bool) (lift true) ≠ (lift true)
  f-bool u = lift-≠ Bool-true≠false ((! u ∙ ap (f-aux (Lift Bool) (lift true)) lem-Bool)) --
    where
    b : Lift Bool
    b = lift true
    Bool-contr : is-contr (Σ (Lift Bool) (λ b' → b' ≠ b))
    Bool-contr = (lift false , lift-≠ Bool-false≠true) , go
      where
      go : (y : Σ (Lift Bool) (λ b' → b' ≠ b)) → lift false , lift-≠ Bool-false≠true == y
      go (lift true  , p) = ⊥-rec (p idp)
      go (lift false , p) = pair= idp (prop-has-all-paths ¬-is-prop (lift-≠ Bool-false≠true) p)
    lem-Bool : (lem (is-contr (Σ (Lift Bool) (λ b' → b' ≠ b))) is-contr-is-prop) == inl Bool-contr
    lem-Bool with inspect (lem (is-contr (Σ (Lift Bool) (λ b' → b' ≠ b))) is-contr-is-prop)
    lem-Bool | inl x₁ with≡ x₂ = x₂ ∙ ap inl (prop-has-all-paths is-contr-is-prop _ _)
    lem-Bool | inr x₁ with≡ x₂ = ⊥-rec (x₁ Bool-contr)
