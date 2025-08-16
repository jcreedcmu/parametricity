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
reltrans {R = R} r p q = transport (λ i → R (p i) (q i)) r

freltrans : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → f x₁ ≡ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → f y₁ ≡ y₂
freltrans {f = f} p q r = reltrans {R = λ x y → f x ≡ y} p q r

freltrans2 : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           → f x₁ ≡ x₂ → x₁ ≡ y₁ → x₂ ≡ y₂ → f y₁ ≡ y₂
freltrans2 {f = f} p q r = sym (cong f q) ∙ p ∙ r

freltrans-eq : {X₁ X₂ : Set} {f : X₁ → X₂} {x₁ y₁ : X₁} {x₂ y₂ : X₂}
           (p : f x₁ ≡ x₂) (q : x₁ ≡ y₁) (r : x₂ ≡ y₂) → freltrans {f = f} p q r ≡ freltrans2 p q r
freltrans-eq p q r = {!!}



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

 -- replace relation with function
 p1 : (X₁ X₂ : Set) (f : X₁ → X₂)
    (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (s : S¹) → f (η₁ s) ≡ (η₂ s))
    (s : S¹)
    → reltrans {R = λ x y → f x ≡ y} (h* (λ x y → f x ≡ y) η₁ η₂ η* (η₁ s) (η₂ s) (η* s)) (p η₁ s) (p η₂ s) ≡ η* s
 p1 X₁ X₂ f η₁ η₂ η* s = p* X₁ X₂ (λ x y → f x ≡ y) η₁ η₂ η* s

 -- assume equal functions instead of pointwise equal functions (i.e. "unapply extensionality")
 p2 : (X₁ X₂ : Set) (f : X₁ → X₂)
    (η₁ : S¹ → X₁) (η₂ : S¹ → X₂) (η* : (λ (s : S¹) → f (η₁ s)) ≡ η₂)
    (s : S¹)
    → reltrans {R = λ x y → f x ≡ y} (h* (λ x y → f x ≡ y) η₁ η₂ (λ s i → η* i s) (η₁ s) (η₂ s) (λ i → η* i s)) (p η₁ s) (p η₂ s) ≡ (λ i → η* i s)
 p2 X₁ X₂ f η₁ η₂ η* s = p* X₁ X₂ (λ x y → f x ≡ y) η₁ η₂ (λ s i → η* i s) s

 -- replace η₂ with what it must be
 p3 : (X₁ X₂ : Set) (f : X₁ → X₂)
    (η₁ : S¹ → X₁) (s : S¹)
    → reltrans {R = λ x y → f x ≡ y} (h* (λ x y → f x ≡ y) η₁ (f ∘ η₁) (λ s → refl) (η₁ s) ((f ∘ η₁) s) refl) (p η₁ s) (p (f ∘ η₁) s) ≡ refl
 p3 X₁ X₂ f η₁ s = p* X₁ X₂ (λ x y → f x ≡ y) η₁ (f ∘ η₁) (λ s → refl) s

 -- try replacing X₁ with S¹, η₁ with id
 p4 : (X₂ : Set) (f : S¹ → X₂)
     (s : S¹)
    → reltrans {R = λ x y → f x ≡ y} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s) ≡ refl
 p4 X₂ f s = p* S¹ X₂ (λ x y → f x ≡ y) id f (λ s → refl) s

 -- try using freltrans
 p5 : (X₂ : Set) (f : S¹ → X₂)
     (s : S¹)
    → freltrans {f = f} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s) ≡ refl
 p5 X₂ f s = p* S¹ X₂ (λ x y → f x ≡ y) id f (λ s → refl) s

 -- lemma for the below
 p6a : (X₂ : Set) (f : S¹ → X₂) (s : S¹) →
      freltrans {f = f} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s)
    ≡ freltrans2 {f = f} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s)
 p6a X₂ f s = (freltrans-eq {f = f} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s))

 -- try using freltrans2
 p6 : (X₂ : Set) (f : S¹ → X₂)
     (s : S¹)
    → freltrans2 {f = f} (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) (p id s) (p f s) ≡ refl
 p6 X₂ f s = sym (p6a X₂ f s) ∙ p* S¹ X₂ (λ x y → f x ≡ y) id f (λ s → refl) s

 -- expand out def'n of freltrans2
 p7 : (X₂ : Set) (f : S¹ → X₂) (s : S¹)
    → sym (cong f (p id s)) ∙ (h* (λ x y → f x ≡ y) id f (λ s → refl) (id s) (f s) refl) ∙ (p f s) ≡ refl
 p7 X₂ f s = sym (p6a X₂ f s) ∙ p* S¹ X₂ (λ x y → f x ≡ y) id f (λ s → refl) s

 -- rename
 p8 : (X₂ : Set) (η₂ : S¹ → X₂) (s : S¹)
    → sym (cong η₂ (p id s)) ∙ (h* (λ x y → η₂ x ≡ y) id η₂ (λ s → refl) (id s) (η₂ s) refl) ∙ (p η₂ s) ≡ refl
 p8 X₂ η₂ s = sym (p6a X₂ η₂ s) ∙ p* S¹ X₂ (λ x y → η₂ x ≡ y) id η₂ (λ s → refl) s

 -- lemma for the below
 p9a : {A : Set} {a b c : A} (p : b ≡ a) (q : b ≡ c) (r : c ≡ a) → sym p ∙ q ∙ r ≡ refl → r ≡ sym q ∙ p
 p9a = {!!}

 -- rearrange
 p9 : (X₂ : Set) (η₂ : S¹ → X₂) (s : S¹)
    → p η₂ s ≡ (sym (h* (λ x y → η₂ x ≡ y) id η₂ (λ s → refl) (id s) (η₂ s) refl)) ∙ cong η₂ (p id s)
 p9 X₂ η₂ s = p9a (cong η₂ (p id s)) (h* (λ x y → η₂ x ≡ y) id η₂ (λ s → refl) (id s) (η₂ s) refl) (p η₂ s) (p8 X₂ η₂ s)
