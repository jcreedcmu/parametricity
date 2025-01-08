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
 module _ (R : Set) (A : {t : T} (e : E t) → Set)
        (f : (r : R) {t : T} (e : E t) → A e) where
  open Interval.Gel.main D S {A = A} R f
  RelHom = Interval.Functoriality.RelHom D S R R f f
  FuncThm : ((t : T) → Gel t → Gel t) ≅ RelHom
  -- XXX many unfulfilled discreteness obligations here
  FuncThm = Interval.Functoriality.thm D S R R {!!} {!!} {!!} {!!} {!!} {!!} f f
  rthm : (zr : R) (zs : RelHom) → (t : T) → Gel t
  rthm zr zs t = cnat (Gel t) (gel zr t) (invIsEq (FuncThm .snd) zs t)

-- rthm : (cnat : (X : Set) → X → (X → X) → X) →
--        (R : Set) (A' : two → Set) (f : (r : R) (x : two) → A' x)
--        (z : (x : two) → A' x) (s : (x : two) → A' x → A' x)
--        (spres : (r : R) → {!!}
-- rthm = {!!}

fthm : (cnat : (X : Set) → X → (X → X) → X) →
      (A B : Set) (f : A → B) (za : A)
      (sa : A → A) (sb : B → B) (compat : (a : A) → f (sa a) ≡ sb (f a))
      → f (cnat A za sa) ≡ cnat B (f za) sb
fthm = {!!}
