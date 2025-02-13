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

-- At the very, very outside we assume someone chose the shape
-- of parametricity we're working with; S = 2 means binary relations.
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
    (𝕀 : W → Set) (embed : S → 𝕀 e) (⋯ maybe also assume that isEquiv embed ⋯)
𝕀 is the interval type, which is substructural, in that it is indexed
by w. We assume that at the empty type there at least a way of getting
S into 𝕀 e; perhaps even 𝕀 e ≡ S.

This is a provisional guess at what I want to assume about 𝕀. Another
alternative that seems about as reasonable is that we can *always*
(i.e. for any w) get S into 𝕀 w, maybe as an embedding, and at e that
map then turns into an equivalence. I'm waiting for theorems to show
up to force my hand. It was attempts to construct a universe that made
me think that 𝕀 turning into exactly S might be what I want. This
seems to give a lot of control, as a copy of 𝕀 glued to neighboring
pieces of typal material sort of conveniently "disappears".

-}

module _ (R : Set) (A : S → Set) (f : (r : R) (s : S) → A s) where
 module _ (W : Set) (e : W) (𝕀 : W → Set) (embed : S → 𝕀 e) where
  data Gel : (w : W) (i : 𝕀 w) → Set where
      gstrand : (w : W) (i : 𝕀 w) (r : R) → Gel w i
      gpoint : (s : S) (a : A s) → Gel e (embed s)
      gpath : (s : S) (r : R) → gstrand e (embed s) r ≡ gpoint s (f r s)
