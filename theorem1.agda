{-# OPTIONS --without-K --rewriting #-}

module theorem1 where

open import HoTT
open import preliminaries

theorem-1-A : (f : (X : U) → X → X) → endomap-natural f → ¬ ((x : Bool) → f Bool x == x) → LEM
theorem-1-A f k q P u with inspect (f (P ⊔ Unit) (inr unit))
theorem-1-A f k q P u | inl p with≡ _ = inl p
theorem-1-A f k q P u | inr unit with≡ z = inr (claim-C z)
  where
  claim-A : ¬ ((f Bool true == true) × (f Bool false == false))
  claim-A (z , w) = q o
    where
    o : (x : Bool) → f Bool x == x
    o true = z
    o false = w
  claim-B : (f Bool true == false) ⊔ (f Bool false == true)
  claim-B with inspect (f Bool true) | inspect (f Bool false)
  claim-B | true with≡ r | true with≡ s = inr s
  claim-B | false with≡ r | false with≡ s = inl r
  claim-B | false with≡ r | true with≡ s = inl r
  claim-B | true with≡ r | false with≡ s = ⊥-rec (claim-A (r , s))
  claim-C-l : (f Bool true == false) → f (P ⊔ Unit) (inr unit) == inr unit → ¬ P
  claim-C-l j z p = inl≠inr p unit (
    inl p =⟨ idp ⟩
    –> e false =⟨ ap (–> e) (! j) ⟩
    –> e (f Bool true) =⟨ k Bool (P ⊔ Unit) e true ⟩
    f (P ⊔ Unit) (–> e true) =⟨ z ⟩
    inr unit =∎)
    where
    e : Bool ≃ P ⊔ Unit
    e = equiv
      (λ {true → inr unit ; false → inl p})
      (λ {(inl _) → false ; (inr _) → true})
      (λ {(inl v) → ap inl (prop-has-all-paths u p v) ; (inr unit) → idp})
      (λ {true → idp ; false → idp})
  claim-C-r : (f Bool false == true) → f (P ⊔ Unit) (inr unit) == inr unit → ¬ P
  claim-C-r j z p = inl≠inr p unit (
    inl p =⟨ idp ⟩
    –> e true =⟨ ap (–> e) (! j) ⟩
    –> e (f Bool false) =⟨ k Bool (P ⊔ Unit) e false ⟩
    f (P ⊔ Unit) (–> e false) =⟨ z ⟩
    inr unit =∎)
    where
    e : Bool ≃ P ⊔ Unit
    e = equiv
      (λ {false → inr unit ; true → inl p})
      (λ {(inl _) → true ; (inr _) → false})
      (λ {(inl v) → ap inl (prop-has-all-paths u p v) ; (inr unit) → idp})
      (λ {false → idp ; true → idp})
  claim-C : f (P ⊔ Unit) (inr unit) == inr unit → ¬ P
  claim-C with claim-B
  claim-C | inl i = claim-C-l i
  claim-C | inr i = claim-C-r i

theorem-1-B : {{_ : FUNEXT}} → LEM → Σ ((X : U) → X → X) (λ f → endomap-natural f × ¬ ((x : Bool) → f Bool x == x))
theorem-1-B lem = f , (f-natural , f-bool)
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
  f-bool : ¬ ((x : Bool) → f Bool x == x)
  f-bool u = Bool-true≠false (! (u true) ∙ (lem-Bool |in-ctx f-aux Bool true))
    where
    b : Bool
    b = true
    Bool-contr : is-contr (Σ Bool (λ b' → b' ≠ b))
    Bool-contr = (false , Bool-false≠true) , go
      where
      go : (y : Σ Bool (λ b' → b' ≠ b)) → false , Bool-false≠true == y
      go (true  , p) = ⊥-rec (p idp)
      go (false , p) = pair= idp (prop-has-all-paths ¬-is-prop Bool-false≠true p)
    lem-Bool : (lem (is-contr (Σ Bool (λ b' → b' ≠ b))) is-contr-is-prop) == inl Bool-contr
    lem-Bool with inspect (lem (is-contr (Σ Bool (λ b' → b' ≠ b))) is-contr-is-prop)
    lem-Bool | inl x₁ with≡ x₂ = x₂ ∙ ap inl (prop-has-all-paths is-contr-is-prop _ _)
    lem-Bool | inr x₁ with≡ x₂ = ⊥-rec (x₁ Bool-contr)
