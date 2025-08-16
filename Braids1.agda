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

 data S+ : Set where
  inl : S+
  inr : S¹ → S+

 split : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂) → S+ → X₂
 split η₂ x₂ inl = x₂
 split η₂ x₂ (inr s) = η₂ s

 h_values : {X₂ : Set} (η₂ : S¹ → X₂) (x₂ : X₂) → h η₂ x₂ ≡ split η₂ x₂ (h inr inl)
 h_values η₂ x₂ = h* (λ x y → y ≡ split η₂ x₂ x) inr η₂ (λ s → refl) inl x₂ refl
