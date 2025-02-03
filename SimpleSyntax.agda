{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module SimpleSyntax where

postulate
 ♯ : ∀ {ℓ} → Type ℓ → Type ℓ
 ι : ∀ {ℓ} {A : Type ℓ} → A → ♯ A
module Param {ℓ ℓ' ℓ'' : Level}
         (A : Type ℓ) {S : Type ℓ'} (B : S → Type ℓ'')
         (M : (s : S) → A → B s)
 where
 postulate
  Gel : ♯ S → Type ℓ''
  Gel-ι : (s : S) → Gel (ι s) ≡p B s
  {-# REWRITE Gel-ι #-}
  gel : (a : A) (s' : ♯ S) → Gel s'
  gel-ι : (a : A) (s : S) → gel a (ι s) ≡p M s a
  {-# REWRITE gel-ι #-}
  ungel : ((s' : ♯ S) → Gel s') → A

  gelβ : (a : A) → ungel (λ s' → gel a s') ≡p a
  {-# REWRITE gelβ #-}
  gelη : (f : (s' : ♯ S) → Gel s') (s' : ♯ S) → gel (ungel f) s' ≡p f s'
  {-# REWRITE gelη #-}

 H : (f : (s' : ♯ S) → Gel s') (s : S) → M s (ungel f) ≡p f (ι s)
 H f s = symp (gel-ι (ungel f) s)

data two : Type where
 t0 t1 : two

module _ (M : (X : Type) → X → X) (R : Type) (A : two → Type) (f : (t : two) → R → A t) (r : R) where
 open Param R A f

 r' : R
 r' = ungel (λ s' → M (Gel s') (gel r s'))

 thm : (t : two) → f t r' ≡p M (A t) (f t r)
 thm = {!!}
