{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module HigherOtt where

postulate
 Bd : ∀ {ℓ} (B : Set ℓ) → B → B → Set ℓ
 ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A} (f : A → B) (p : Bd A a a') → Bd B (f a) (f a')

 Bd/U : ∀ {ℓ} {A B : Set ℓ} → Bd (Set ℓ) A B ≡p (A → B → Set ℓ)
 {-# REWRITE Bd/U #-}
 Bd/× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p p' : A × B} → Bd (A × B) p p' ≡p
      Bd A (fst p) (fst p') × Bd B (snd p) (snd p')
 {-# REWRITE Bd/× #-}
 Bd/→ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f f' : A → B} → Bd (A → B) f f' ≡p
      ({a a' : A} → Bd A a a' → Bd B (f a) (f' a'))
 {-# REWRITE Bd/→ #-}


 -- (f a) → (f a') → Set

Bdd : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') {a a' : A} (p : Bd A a a') → B a → B a' → Set ℓ'
Bdd B p ba ba' = ap B p ba ba'

postulate
 -- are f and f' x-generic or x-specific?
 Bdd/→ : ∀ {ℓ0 ℓ ℓ'} {X : Set ℓ0} {A : X → Set ℓ} {B : X → Set ℓ'} {f f' : (x : X) (a : A x) → B x }
            {a a' : (x : X) → A x} (p : (x : X) → Bd (A x) (a x) (a' x)) {x x' : X} (x~ : Bd X x x')
      → Bdd {A = X} (λ x → A x → B x) x~ (f x) (f' x') ≡p ({a : A x} {a' : A x'} → Bdd A x~ a a' → Bdd B x~ (f x a) (f' x' a'))
 -- {-# REWRITE Bdd/→ #-} -- can't make this a rewrite rule, as I'm effectively trying to do HOAS!

 Bd/Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f f' : (a : A) → B a} → Bd ((a : A) → B a) f f' ≡p
      ({a a' : A} (p : Bd A a a') → Bdd B p (f a) (f' a'))
 {-# REWRITE Bd/Π #-}

postulate
 apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a a' : A} (f : (a : A) → B a) (p : Bd A a a') → Bdd B p (f a) (f a')

foo : {A B : Set} (id : (X : Set) → X → X) (R : A → B → Set) (a : A) (b : B) (r : R a b)
      → ap {A = Set} {B = Set} (λ z → z → z) R (id A) (id B)
foo id R a b r = apd id R
