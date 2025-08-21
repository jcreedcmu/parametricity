{-# OPTIONS --cubical #-}




open import Function.Base

open import Cubical.Foundations.Prelude hiding (Path; J)
open import Cubical.Data.Sigma
open import Cubical.Core.Primitives
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1

module Braids1 where

{-

 The purpose of this file is to carefully verify the HoTT reasoning
 involved in showing that *if* we had the appropriate parametricity
 theorem, we'd know that any inhabitant of

   (X : Set) (η : S¹ → X) → (h : X → X) × (h ∘ η ≡ η)

 must be λ X η → ⟨ λx → x, refl ⟩.

 Equivalently, if we had parametric

   h : (X : Set) (η : X → X) (x : X) → X
   p : (X : Set) (η : X → X) (s : S¹) → h (η s) ≡ η s

 Then we could prove

  h! : h X η ≡ id
  p! : p X η s ≡ refl (over the path h!)

 The meaning of h and p being parametric is witnessed by the terms h*
 and p* below, respectively.

-}


postulate
 h : {X : Set} (η : S¹ → X) (x : X) → X
 p : {X : Set} (η : S¹ → X) (s : S¹) → h η (η s) ≡ η s
 h* : {X₁ X₂ : Set} (R : X₁ → X₂ → Set)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
       (x₁ : X₁) (x₂ : X₂) → R x₁ x₂ → R (h η₁ x₁) (h η₂ x₂)

reltrans : (X₁ X₂ : Set) (R : X₁ → X₂ → Set) (x₁ y₁ : X₁) (x₂ y₂ : X₂)
           → R x₁ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → R y₁ y₂
reltrans X₁ X₂ R x₁ y₁ x₂ y₂ r p q = transport (λ i → R (p i) (q i)) r

freltrans : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → f x₁ ≡ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → f y₁ ≡ y₂
freltrans {f = f} p q r = reltrans _ _ (λ x y → f x ≡ y) _ _ _ _ p q r

freltrans2 : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → f x₁ ≡ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → f y₁ ≡ y₂
freltrans2 {f = f} p q r = sym (cong f q) ∙ p ∙ r

freltrans-eq : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           (p : f x₁ ≡ x₂) (q : x₁ ≡ y₁) (r : x₂ ≡ y₂) → freltrans2 {f = f} p q r ≡ freltrans p q r
freltrans-eq = {!!}

postulate
 p* :
    (X₁ X₂ : Set) (R : X₁ → X₂ → Set)
    (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
    (s : S¹)
    → reltrans X₁ X₂ R (h η₁ (η₁ s)) (η₁ s) (h η₂ (η₂ s)) (η₂ s)
       (h* R η₁ η₂ η* (η₁ s) (η₂ s) (η* s)) (p η₁ s) (p η₂ s) ≡ η* s

data S+ : Set where
 inl : S+
 inr : S¹ → S+

-- just a convenient name for the S+ eliminator
split : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂) → S+ → X₂
split η₂ x₂ inl = x₂
split η₂ x₂ (inr s) = η₂ s

spls : {X : Set} (η : S¹ → X) (s : S¹) → S+ → X → Type
spls η s a b = split η (η s) a ≡ b

-- This is an important lemma on the way to proving h!. We find that
-- the values of h globally are determined by one particular value,
-- that of `h {S+} inr inl`.
h_values : {X : Set} (η : S¹ → X) (x : X) → split η x (h inr inl) ≡ h η x
h_values η x = h* (λ a b → split η x a ≡ b) inr η (λ s → refl) inl x refl


p*-lem : (X : Set) (η : S¹ → X) (s : S¹)
    → freltrans {f = split η (η s)} (h* (spls η s) inr η (λ s → refl) (inr s) (η s) refl) (p inr s) (p η s) ≡ refl
p*-lem X η s = p* S+ X (spls η s) inr η (λ s → refl) s

p*-lem2 : (X : Set) (η : S¹ → X) (s : S¹)
    → sym (cong (split η (η s)) (p inr s)) ∙ (h* (spls η s) inr η (λ s → refl) (inr s) (η s) refl) ∙ (p η s) ≡ refl
p*-lem2 X η s = freltrans-eq {f = split η (η s)} (h* (spls η s) inr η (λ s → refl) (inr s) (η s) refl) (p inr s) (p η s) ∙ (p*-lem X η s)

p*-lem3 : (X : Set) (η : S¹ → X) (s : S¹)
    →  (h* (spls η s) inr η (λ s → refl) (inr s) (η s) refl) ∙ (p η s) ≡ (cong (split η (η s)) (p inr s))
p*-lem3 X η s = {!!}

p*-lem4 : (X : Set) (η : S¹ → X) (s : S¹)
    → p η s ≡ sym (h* (spls η s) inr η (λ s → refl) (inr s) (η s) refl) ∙ (cong (split η (η s)) (p inr s))
p*-lem4 X η s = {!!}




k : h {S+} inr inl ≡ inl
k = {!!}

h! : {X : Set} (η : S¹ → X) (x : X) → h η x ≡ x
h! η x = sym (h_values η x) ∙ cong (split η x) k


p!-lemma2 : {X : Set} (η : S¹ → X) (s : S¹) → sym (h* (spls η s) inr η (λ s → refl) inl (η s) refl) ∙ cong (split η (η s)) k ≡ p η s
p!-lemma2 = {!!}

p!-lemma : {X : Set} (η : S¹ → X) (s : S¹) → h! η (η s) ≡ p η s
p!-lemma η s = p!-lemma2 η s

sq-lemma : {A : Set} {a b : A} (p : a ≡ b) → Square p refl p refl
sq-lemma p i j = p (i ∨ j)

-- diagram for p!:
-- https://q.uiver.app/#q=WzAsNCxbMCwwLCJoXFwgKFxcZXRhXFwgcykiXSxbMSwwLCJcXGV0YVxcIHMiXSxbMCwxLCJcXGV0YVxcIHMiXSxbMSwxLCJcXGV0YVxcIHMiXSxbMCwxLCJwXFwgcyIsMCx7ImxldmVsIjoyLCJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzIsMywiXFxtYXRoc2Z7cmVmbH0iLDIseyJsZXZlbCI6Miwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFswLDIsImhfIVxcIChcXGV0YVxcIHMpIiwyLHsibGV2ZWwiOjIsInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMSwzLCJcXG1hdGhzZntyZWZsfSIsMCx7ImxldmVsIjoyLCJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV1d

-- Goal:
p! : {X : Set} (η : S¹ → X) (s : S¹) → Square (h! η (η s)) refl (p η s) refl
p! {X} η s = subst (λ z → Square (h! η (η s)) refl z refl) (p!-lemma η s) (sq-lemma (h! η (η s)))
