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
open import Function.Base

module Thinness where

data two : Set where
 t0 t1 : two

postulate
 -- paths of unbounded length
 _⇒_ : {A : Set} (a a' : A) → Set

module _ (A : Set) where
 data Tele : Set
 Ball : Tele → Set

 data Tele where
  tnil : Tele
  tcons : (t : Tele) (b1 b2 : Ball t) → Tele
 Ball tnil = A
 Ball (tcons t src tgt) = src ⇒ tgt

postulate
 isFull : {A : Set} {t : Tele A} (b : Ball A t) → Set -- is a prop


record GoodEdge : Set₁ where constructor mkGoodEdge ; field
 A : Set
 bd : two → A
 path : bd t0 ⇒ bd t1
 full : isFull {!!}

module _ (ge1 : two → GoodEdge) where
 postulate
  mergedSpace1 : Set
  mergedBd1 : two → mergedSpace1

 -- record GoodEdge2 : Set₁ where constructor mkGoodEdge2 ; field
 --  A : Set
 --  bd : {!!}
