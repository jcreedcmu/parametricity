{-# OPTIONS --cubical #-}

-- open import Agda.Primitive
-- open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
-- open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)

-- open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat hiding (Unit ; _·_)
-- open import Cubical.Data.Empty renaming (rec to aborti)
-- open import Cubical.Data.Equality using () renaming (sym to symp)
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Functions.Embedding



open import Function.Base

open import Cubical.Foundations.Prelude hiding (Path)
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

B : Set₁
B = {X : Set} (η : S¹ → X) (x : X) → X

B' : (h : B) → Set₁
B' h = {X : Set} (η : S¹ → X) (s : S¹) → h η (η s) ≡ η s

P₁ : (h : B) → Set₁
P₁ h = {X₁ X₂ : Set} (R : X₁ → X₂ → Set)
       (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
       (x₁ : X₁) (x₂ : X₂) → R x₁ x₂ → R (h η₁ x₁) (h η₂ x₂)

reltrans : {X₁ X₂ : Set} {R : X₁ → X₂ → Set} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → R x₁ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → R y₁ y₂
reltrans = {!!}

P₂ : (h : B) (p : B' h) → Set₁
P₂ h p =
    (X₁ X₂ : Set) (R : X₁ → X₂ → Set)
    (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → R (η₁ s) (η₂ s))
    (s : S¹)
    → reltrans {X₁} {X₂} {- clearly wrong: -} {λ _ _ → R (η₁ s) (η₂ s)} (η* s) (p η₁ s) (p η₂ s) ≡ η* s
