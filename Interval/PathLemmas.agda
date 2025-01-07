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
