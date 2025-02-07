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

module Balls where

data Void : Set where

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

data Tele : Set₁
Ball : Tele → Set₁
BallDom : Tele → Set

data Tele where
 tnil : Tele
 tcons : (t : Tele) (b1 b2 : Ball t) → Tele

Ball t = Σ[ Cr ∈ Set ] (BallDom t → Cr)
BallDom tnil = Void
BallDom (tcons t b1 b2) = Pushout (b1 .snd) (b2 .snd)

-- Ball tnil = Σ[ Cr ∈ Set ] void → Cr -- just a set, ideally Unit
-- Ball (tcons tnil b1 b2) = Σ[ Cr ∈ Set ] (b1 .fst + .b2 fst) → Cr  -- a set with two points
