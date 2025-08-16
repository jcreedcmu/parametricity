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

 Then we could prove h X η ≡ id, and p X η x s ≡ refl.

-}

-- The type of functions induced by a choice of X and η
H : Set₁
H = {X : Set} (η : S¹ → X) (x : X) → X

-- The type of proofs that h : H preserves η
P : (h : H) → Set₁
P h = {X : Set} (η : S¹ → X) (s : S¹) → h η (η s) ≡ η s

-- The type of proofs that an h : H is in the relation
H* : (h : H) → Set₁
H* h = {X₁ X₂ : Set} (R : X₁ → X₂ → Set)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
       (x₁ : X₁) (x₂ : X₂) → R x₁ x₂ → R (h η₁ x₁) (h η₂ x₂)

reltrans : {X₁ X₂ : Set} {R : X₁ → X₂ → Set} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → R x₁ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → R y₁ y₂
reltrans = {!!}

P* : (h : H) (p : P h) (h* : H* h) → Set₁
P* h p h* =
    (X₁ X₂ : Set) (R : X₁ → X₂ → Set)
    (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
    (s : S¹)
    → reltrans {R = R} (h* R η₁ η₂ η* (η₁ s) (η₂ s) (η* s)) (p η₁ s) (p η₂ s) ≡ η* s

module _ (h : H) (p : P h) (h* : H* h) (p* : P* h p h*) where
 h1 : {X₁ X₂ : Set} (R : X₁ → X₂ → Set)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
       (x₁ : X₁) (x₂ : X₂) → R x₁ x₂ → R (h η₁ x₁) (h η₂ x₂)
 h1 R η₁ η₂ η* x₁ x₂ x* = h* R η₁ η₂ η* x₁ x₂ x*

 h2 : {X₁ X₂ : Set} (f : X₁ → X₂)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → f (η₁ s) ≡ (η₂ s))
       (x₁ : X₁) (x₂ : X₂) → f x₁ ≡ x₂ → f (h η₁ x₁) ≡ (h η₂ x₂)
 h2 f η₁ η₂ η* x₁ x₂ x* = h* (λ x y → f x ≡ y) η₁ η₂ η* x₁ x₂ x*

 h3 : {X₁ X₂ : Set} (f : X₁ → X₂)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (λ (s : S¹) → f (η₁ s)) ≡ η₂)
       (x₁ : X₁) (x₂ : X₂) → f x₁ ≡ x₂ → f (h η₁ x₁) ≡ (h η₂ x₂)
 h3 f η₁ η₂ η* x₁ x₂ x* = h* (λ x y → f x ≡ y) η₁ η₂ (λ s i → η* i s) x₁ x₂ x*

 h4 : {X₁ X₂ : Set} (f : X₁ → X₂)
       (η₁ : S¹ → X₁) (x₁ : X₁) → f (h η₁ x₁) ≡ h (f ∘ η₁) (f x₁)
 h4 f η₁ x₁ = h* (λ x y → f x ≡ y) η₁ (f ∘ η₁) (λ s → refl) x₁ (f x₁) refl

 data S+ : Set where
  inl : S+
  inr : S¹ → S+

 h5 : {X₂ : Set} (f : S+ → X₂)
       (η₁ : S¹ → S+) (x₁ : S+) → f (h η₁ x₁) ≡ h (f ∘ η₁) (f x₁)
 h5 f η₁ x₁ = h* (λ x y → f x ≡ y) η₁ (f ∘ η₁) (λ s → refl) x₁ (f x₁) refl

 mapin : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂) → S+ → X₂
 mapin η₂ x₂ inl = x₂
 mapin η₂ x₂ (inr s) = η₂ s

 h6 : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂)
       (η₁ : S¹ → S+) (x₁ : S+) → (mapin η₂ x₂) (h η₁ x₁) ≡ h ((mapin η₂ x₂) ∘ η₁) ((mapin η₂ x₂) x₁)
 h6 η₂ x₂ η₁ x₁ = h* (λ x y → mapin η₂ x₂ x ≡ y) η₁ (mapin η₂ x₂ ∘ η₁) (λ s → refl) x₁ (mapin η₂ x₂ x₁) refl

 h7 : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂)
        (x₁ : S+) → (mapin η₂ x₂) (h inr x₁) ≡ h ((mapin η₂ x₂) ∘ inr) ((mapin η₂ x₂) x₁)
 h7 η₂ x₂ x₁ = h* (λ x y → mapin η₂ x₂ x ≡ y) inr (mapin η₂ x₂ ∘ inr) (λ s → refl) x₁ (mapin η₂ x₂ x₁) refl

 h8 : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂)
         → mapin η₂ x₂ (h inr inl) ≡ h η₂ x₂
 h8 η₂ x₂ = h* (λ x y → mapin η₂ x₂ x ≡ y) inr η₂ (λ s → refl) inl x₂ refl
