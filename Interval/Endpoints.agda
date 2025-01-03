{-# OPTIONS --cubical --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base
import Interval.Gel
import PropSigmaReduce

{-
 - The point of this is to show that when t is an endpoint (i.e. E t holds)
 - then the type Gel t is isomorphic to the prescribed endpoint set.
 - FIXME: adapt proof in ../prop-family-sigma.agda
 -}

module Interval.Endpoints where

module main {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

 module _ {A : {t : T} (e : E t) → Set ℓ} (R : Set ℓ) (f : (r : R) {t : T} (e : E t) → A e) where
  Gel = Interval.Gel.main.Gel {ℓ1} {ℓ2} D S R f

  sumeq : {t : T} → (Σ[ e ∈ E t ] Gel t) ≅ (Σ[ e ∈ E t ] A e)
  sumeq = {!!} -- isoToEquiv (Cubical.Foundations.Isomorphism.iso fore back section retract)

  Gel-endpoints : {t : T} (e : E t)→ Gel t ≅ A e
  Gel-endpoints {t} e = PropSigmaReduce.thm  (E t) (λ _ → Gel t) A (EndIsProp t) sumeq e
