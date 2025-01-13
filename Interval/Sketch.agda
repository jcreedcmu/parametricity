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

module Interval.Sketch where

data Tree : Set where
 leaf : Tree
 arrow : Tree → Tree → Tree

module _ (A : Set) where
 interp : Tree → Set
 interp leaf = A
 interp (arrow t u) = (interp t) → (interp u)

postulate
 ♯2 : Set
 p0 p1 : ♯2
 Gel : {A B : Set} (R : A → B → Set) → Set

module _ (A B : Set) (R : A → B → Set) where

 inrel : (t : Tree) → interp A t → interp B t → Set
 inrel leaf a b = R a b
 inrel (arrow t u) f g = (a : interp A t) (b : interp B t)
                   → inrel t a b → inrel u (f a) (g b)


 parametricity : (t : Tree) (pf : (A : Set) → interp A t)
                 → inrel t (pf A) (pf B)
 parametricity t pf = {!pf ♯2!}
