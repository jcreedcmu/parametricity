{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Functions.Embedding
open import Cubical.HITs.Pushout
open import Function.Base

module HoasIsh (S : Set) where

data Void : Set where

abort : (A : Set) → Void → A
abort A ()

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

{-

The idea I wanted to explore here was the perhaps overrecursive notion
"parametricity via parametricity". I am calling it HOAS-ish in the
hope that there actually is an interesting idea here that takes you
from "a little parametricity" to "a lot of parametricity" the way HOAS
takes you from "just one notion of function binding" to "lots of
different notions of binding".

I want to use the "input" parametricity to justify a construction that
is meant to simulate substructurality.

Some constructions will be in the context of
    (W : Set) (e : W) (⋯ maybe also W is a monoid ⋯)
W is the type of worlds. There is an empty world e.

Some constructions will further be in the context of
    (𝕀 : W → Set)
𝕀 is the interval type, which is substructural, in that it is indexed
by w. I think the "boundary set" is to be identified with 𝕀 e. It may
be that I wand to assume that I can embed the boundary set in 𝕀 w for
other w, but I haven't needed this yet.

-}

module GelType (W : Set) (e : W) (𝕀 : W → Set)
               (R : Set) (A : (i : 𝕀 e) → Set) (f : (s : 𝕀 e) (r : R) → A s)
               where

  data Gel : (w : W) (i : 𝕀 w) → Set where
      gel : (w : W) (i : 𝕀 w) (r : R) → Gel w i
      gbound : (s : 𝕀 e) (a : A s) → Gel e s
      gpath : (s : 𝕀 e) (r : R) → gel e s r ≡ gbound s (f s r)

  postulate
    ungel : ((w : W) (i : 𝕀 w) → Gel w i) → R
    bound-equiv : (s : 𝕀 e) → isEquiv (gbound s)
    ungel-bd : (g : (w : W) (i : 𝕀 w) → Gel w i) (s : 𝕀 e)
         → f s (ungel g) ≡ invIsEq (bound-equiv s) (g e s)

module FreeThm
  (W : Set) (e : W) (𝕀 : W → Set)
  (R : Set) (A : (i : 𝕀 e) → Set) (f : (s : 𝕀 e) (r : R) → A s)
  (idf : (X : Set) → X → X) (r : R) where
 module _  where
  open GelType W e 𝕀 R A f

  package : (w : W) (i : 𝕀 w) → Gel w i
  package w i = idf (Gel w i) (gel w i r)

  output : R
  output = ungel package
