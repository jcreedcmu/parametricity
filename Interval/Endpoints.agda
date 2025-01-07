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
  open Interval.Gel.main.gel {ℓ1} {ℓ2} D S R f

  private
   fore : {t : T} → (Σ[ e ∈ E t ] Gel t) → (Σ[ e ∈ E t ] A e)
   fore (e , gstrand r) = e , (f r e)
   fore (e , gpoint {e = e'} a) = e' , a
   fore {t} (e , gpath {e = e'} r i) = EndIsProp t e' e i , f r (EndIsProp t e' e i)

   back : {t : T} → (Σ[ e ∈ E t ] A e) → (Σ[ e ∈ E t ] Gel t)
   back (e , a) = (e , gpoint a)

   sect : {t : T} → (g : Σ[ e ∈ E t ] A e) → fore (back g) ≡ g
   sect s i = s

   retr : {t : T} → (g : Σ[ e ∈ E t ] Gel t) → back (fore g) ≡ g
   retr (e , gstrand r) i = e , (gpath {e = e}r i)
   retr {t} (e , gpoint {e = e'} a) i = EndIsProp t e' e i , gpoint a
   retr {t} (e , gpath {e = e'} r j) i = EndIsProp t e' e (i ∨ j) , {!!}

  sumeq : {t : T} → (Σ[ e ∈ E t ] Gel t) ≅ (Σ[ e ∈ E t ] A e)
  sumeq =  isoToEquiv (Cubical.Foundations.Isomorphism.iso fore {!!} {!!} {!!})

  Gel-endpoints : {t : T} (e : E t)→ Gel t ≅ A e
  Gel-endpoints {t} e = PropSigmaReduce.thm  (E t) (λ _ → Gel t) A (EndIsProp t) sumeq e
