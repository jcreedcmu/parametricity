{-# OPTIONS --cubical --rewriting #-}

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
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module Interval.FreeTheorem where

data two : Set where
 t0 : two
 t1 : two

T' : {ℓ1 : Level} (D : Set ℓ1) → Set ℓ1
T' D = D ▻ two
E = End

module _ (cnat : (X : Set) → X → (X → X) → X) (R : Set) where
 D = R
 S = two
 T = T' D

 module stage1 (A : {t : T} (e : E t) → Set)
        (disc-A : (t : T) (e : E t) → bridgeDiscrete T (A e))
        (f : (r : R) {t : T} (e : E t) → A e) where
  open Interval.Gel.main D S {A = A} R f renaming (ungel to ungel')
  RelHom = Interval.Functoriality.RelHom D S R R f f

  -- XXX unfulfilled discreteness obligations here
  disc-R : bridgeDiscrete T R
  disc-R = ▻Discrete {D = R} {S = two}

  ungel = ungel' disc-R disc-A

  FuncThm : ((t : T) → Gel t → Gel t) ≅ RelHom
  FuncThm = Interval.Functoriality.thm D S R R disc-R disc-A disc-R disc-A f f

  intoGel : (zr : R) (zs : RelHom) → (t : T) → Gel t
  intoGel zr zs t = cnat (Gel t) (gel zr t) (invIsEq (FuncThm .snd) zs t)

  intoR : (zr : R) (zs : RelHom) → R
  intoR zr zs = ungel (intoGel zr zs)

 module stage2 (R : Set) (A : two → Set) (f : (r : R) (x : two) → A x) where
  -- RelHom = Interval.Functoriality.RelHom D S R R f f

  -- intoR : (zr : R) (zs : RelHom) → R
  -- intoR = ?

fthm : (cnat : (X : Set) → X → (X → X) → X) →
      (A B : Set) (f : A → B) (za : A)
      (sa : A → A) (sb : B → B) (compat : (a : A) → f (sa a) ≡ sb (f a))
      → f (cnat A za sa) ≡ cnat B (f za) sb
fthm = {!!}
