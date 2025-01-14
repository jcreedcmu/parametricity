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
 ap2 : ∀ {ℓ ℓ'} {A1 A2 : Set ℓ} {B : Set ℓ'} {a1 a1' : A1} {a2 a2' : A2} (f : A1 → A2 → B)
                (p1 : Bd A1 a1 a1') (p2 : Bd A2 a2 a2') → Bd B (f a1 a2) (f a1' a2')
 ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A} (f : A → B) (p : Bd A a a') → Bd B (f a) (f a')
 brefl : ∀ {ℓ'}  {B : Set ℓ'} (f : B) → Bd B f f
 isRefl : ∀ {ℓ ℓ'}  {B : Set ℓ'} (f f' : B) → Bd B f f' → Set ℓ -- levels??

 Bd/U : ∀ {ℓ} {A B : Set ℓ} → Bd (Set ℓ) A B ≡p (A → B → Set ℓ)
 {-# REWRITE Bd/U #-}
 Bd/× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p p' : A × B} → Bd (A × B) p p' ≡p
      Bd A (fst p) (fst p') × Bd B (snd p) (snd p')
 {-# REWRITE Bd/× #-}
 Bd/→ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f f' : A → B} → Bd (A → B) f f' ≡p
      ({a a' : A} → Bd A a a' → Bd B (f a) (f' a'))
 {-# REWRITE Bd/→ #-}

 isRefl/U : ∀ {ℓ} (B C : Set ℓ) (d : Bd (Set ℓ) B C) → isRefl {B = Set ℓ} B C d ≡p
   ( (((b : B) → isContr (Σ C (λ c → d b c)))) × (((c : C) → isContr (Σ B (λ b → d b c)))) )

 -- (f a) → (f a') → Set

Bdd : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') {a a' : A} (p : Bd A a a') → B a → B a' → Set ℓ'
Bdd B p ba ba' = ap B p ba ba'

postulate
 ap/→ : ∀ {ℓ0 ℓ ℓ'} {X : Set ℓ0} {A : X → Set ℓ} {B : X → Set ℓ'}
             (x x' : X) (x~ : Bd X x x')
             {f : (a : A x) → B x } {f' : (a : A x') → B x'}
      → ap (λ x → A x → B x) x~ f f' ≡p ({a : A x} {a' : A x'} → ap A x~ a a' → ap B x~ (f a) (f' a'))
 -- {-# REWRITE Bdd/→ #-} -- can't make this a rewrite rule, as I'm effectively trying to do HOAS!

 Bd/Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f f' : (a : A) → B a} → Bd ((a : A) → B a) f f' ≡p
      ({a a' : A} (p : Bd A a a') → Bdd B p (f a) (f' a'))
 {-# REWRITE Bd/Π #-}

postulate
 apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a a' : A} (f : (a : A) → B a) (p : Bd A a a') → Bdd B p (f a) (f a')

 ap/id : ∀ {ℓ} {A B : Set ℓ} {R : A → B → Set ℓ} →
        ap {a = A} {a' = B} (λ X → X) R ≡p R
 {-# REWRITE ap/id #-}

foo : {A B : Set} (id : (X : Set) → X → X) (R : A → B → Set)
      → ap (λ z → z → z) R (id A) (id B)
foo id R = apd id R

foo-step : (A B : Set) {id : (X : Set) → X → X} (R : A → B → Set)
    → ap (λ z → z → z) R (id A) (id B) ≡p ({a : A} {b : B} → R a b → R (id A a) (id B b))
foo-step A B R = ap/→ A B R

-- module _ where
--  postulate
--   isDiag : ∀ {ℓ} Bd
