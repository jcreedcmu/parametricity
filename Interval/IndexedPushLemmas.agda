{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection
open import Interval.Discreteness

module Interval.IndexedPushLemmas where

data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B)
          : Set (ℓ1 ⊔ ℓ2 ⊔ ℓ3) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  ppath : (c : C) → pinr (g c) ≡ pinl (f c)

Push-left-cong-equiv :
          {ℓ1 ℓ2 ℓ3 : Level}
          {A A' : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B)
          (eq : A ≅ A')
          → Push {A = A} f g ≅ Push {A = A'} (λ c → funIsEq (eq .snd) (f c)) g
Push-left-cong-equiv {ℓ1} {ℓ2} {ℓ3} {A = A} {A'} {C = C} f g eq = isoToEquiv (iso fore back sect retr) where
 fff = funIsEq (eq .snd)
 inv = invIsEq (eq .snd)
 sec = secIsEq (eq .snd)
 ret = retIsEq (eq .snd)

 fore : Push {A = A} f g → Push {A = A'} (λ c → fff (f c)) g
 fore (pinl a) = pinl (fff a)
 fore (pinr b) = pinr b
 fore (ppath c i) = ppath c i

 back : Push {A = A'} (λ c → fff (f c)) g → Push {A = A} f g
 back (pinl a) = pinl (inv a)
 back (pinr b) = pinr b
 back (ppath c i) = (ppath c ∙∙ refl ∙∙ λ j → pinl (ret (f c) (~ i ∨ ~ j))) i

 sect : (g : Push {A = A'} (λ c → fff (f c)) g ) → fore (back g) ≡ g
 sect (pinl a) = λ i → pinl (sec a i)
 sect (pinr b) = λ i → pinr b
 sect (ppath c i) j = hcomp (λ k → λ {
    (i = i0) → ppath c (~ k) ;
    (j = i0) → fore ((doubleCompPath-filler (ppath c) refl (λ j → pinl (ret (f c) (~ i ∨ ~ j))) k i )) ;
    (i = i1) → pinl (commSqIsEq (eq .snd) (f c) (~ k) j) ;
    (j = i1) → ppath c (i ∨ ~ k)
    }) (pinl (fff (f c)))

 retr : (g : Push {A = A} f g) → back (fore g) ≡ g
 retr (pinl a) i = pinl (ret a i)
 retr (pinr b) i = pinr b
 retr (ppath c i) j = hcomp (λ k → λ {
   (i = i0) → ppath c (~ k) ;
   (j = i0) → doubleCompPath-filler (ppath c) refl (λ j → pinl (ret (f c) (~ i ∨ ~ j))) k i  ;
   (i = i1) → pinl (ret (f c) (j ∨ ~ k)) ;
   (j = i1) → ppath c (i ∨ ~ k ) })
  (pinl (f c))
