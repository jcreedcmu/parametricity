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

module HoasIsh where

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

module GelType (W : Set) (emp : W) (𝕀 : W → Set) where
 module _ (R : Set) (A : (i : 𝕀 emp) → Set) (f : (i : 𝕀 emp) (r : R) → A i) where
  data Gel : (w : W) (i : 𝕀 w) → Set where
      gstrand : (w : W) (i : 𝕀 w) (r : R) → Gel w i
      gpoint : (i : 𝕀 emp) (a : A i) → Gel emp i
      gpath : (i : 𝕀 emp) (r : R) → gstrand emp i r ≡ gpoint i (f i r)

{- I could have imagined 𝕁 = Σ W 𝕀, but I think this will be harder to reason about
 - when it comes time to do iterated internalized parametricity! -}
module Hide where
 module _ (𝕁 : Set) (E : 𝕁 → Set) where
  module _ (R : Set) (A : {j : 𝕁} (e : E j) → Set) (f : {j : 𝕁} (e : E j) (r : R) → A e) where
   data Gel (j : 𝕁) : Set where
       gstrand : (r : R) → Gel j
       gpoint : (e : E j) (a : A e) → Gel j
       gpath : (e : E j) (r : R) → gstrand r ≡ gpoint e (f e r)
