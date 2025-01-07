{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.ThreePush
import Interval.Endpoints
open import Function.Base
import Interval.Gel

{-
 - Some more general-purpose lemmas used in Functoriality
 -}
module Interval.PathLemmas where

extendByPath : ∀ {ℓ} {A : Set ℓ} {a b c : A} (p : b ≡ c) → (a ≡ b) ≅ (a ≡ c)
extendByPath {A = A} {a} {b} {c} p = isoToEquiv (iso fore back sect retr) where
 fore : a ≡ b → a ≡ c
 fore q = q ∙ p

 back : a ≡ c → a ≡ b
 back q = q ∙ (sym p)

 sect : (q : a ≡ c) → (q ∙ sym p) ∙ p ≡ q
 sect q = compPathr-cancel p q

 retr : (q : a ≡ b) → (q ∙ p) ∙ sym p ≡ q
 retr q = compPathr-cancel (sym p) q

piIsoCong : ∀ {ℓ} {A : Set ℓ} {B B' : A → Set ℓ}
            (eq : (a : A) → B a ≅ B' a) →
            ((a : A) → B a) ≅ ((a : A) → B' a)
piIsoCong {A = A} {B} {B'} eq = isoToEquiv (iso fore back sect retr) where
 fore : ((a : A) → B a) → ((a : A) → B' a)
 fore f a = funIsEq (eq a .snd) (f a)

 back : ((a : A) → B' a) → ((a : A) → B a)
 back f a = invIsEq (eq a .snd) (f a)

 sect : (f : (a : A) → B' a) → fore (back f) ≡ f
 sect f i a = secIsEq (eq a .snd) (f a) i

 retr : (f : (a : A) → B a) → back (fore f) ≡ f
 retr f i a = retIsEq (eq a .snd) (f a) i

cancelEquiv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {a1 a2 : A}
              (eq : isEquiv f) →
              (f a1 ≡ f a2) ≅ (a1 ≡ a2)
cancelEquiv f {a1} {a2} eq = isoToEquiv (iso fore back sect retr) where
  invf = invIsEq eq

  fore : (f a1 ≡ f a2) → (a1 ≡ a2)
  fore p = sym (retIsEq eq a1) ∙∙ cong invf p ∙∙ retIsEq eq a2

  back : a1 ≡ a2 → (f a1 ≡ f a2)
  back = cong f

  sect : (q : a1 ≡ a2) → fore (back q) ≡ q
  sect q i j = hcomp (λ k → λ {
    (i = i0) → doubleCompPath-filler (sym (retIsEq eq a1)) (cong invf (cong f q)) (retIsEq eq a2) k j ;
    (i = i1) → q j ;
    (j = i0) → retIsEq eq a1 (i ∨ k) ;
    (j = i1) → retIsEq eq a2 (i ∨ k)
   }) (retIsEq eq (q j) i)

  retr : (q : f a1 ≡ f a2) → back (fore q) ≡ q
  retr q i j = hcomp (λ k → λ {
    (i = i0) → f (doubleCompPath-filler (sym (retIsEq eq a1)) (cong invf q) (retIsEq eq a2) k j)  ;
    (i = i1) → secIsEq eq (q j) k  ;
    (j = i0) → commPathIsEq eq a1 (~ i) k ;
    (j = i1) → commPathIsEq eq a2 (~ i) k
   }) (f (invf (q j)) )
