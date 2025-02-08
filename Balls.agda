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

abort : (A : Set) → Void → A
abort A ()

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

module _ where
 -- Forward declarations for mutual recursion:
 data Tele : Set₁
 record Ball (t : Tele) : Set₁
 BallDom : Tele → Set

 -- Definitions:
 data Tele where
  tnil : Tele
  tcons : (t : Tele) (b1 b2 : Ball t) → Tele
 record Ball t where constructor mkBall ; field
   Cr : Set
   Bd : BallDom t → Cr
 open Ball
 BallDom tnil = Void
 BallDom (tcons t b1 b2) = Pushout (b1 .Bd) (b2 .Bd)

-- For example:
--
-- Ball tnil = { Cr : Set, Bd : void → Cr }
-- just a set, ideally Unit
--
-- Ball (tcons tnil b1 b2) = { Cr : Set, (b1 .fst + .b2 fst) → Cr }
-- a set with two points

-- This is the canonical 1-point 0-dimensional ball
c0 : Ball tnil
c0 = mkBall Unit (abort Unit)

-- This is the canonical type of 1-dimensional balls
C1 : Set₁
C1 = Ball (tcons tnil c0 c0)

module _ where
 open Ball
 dom : (P : C1) → P .Cr
 dom P = P .Bd (inl ⋆)

 cod : (P : C1) → P .Cr
 cod P = P .Bd (inr ⋆)


compose : (p1 p2 : C1) → C1
compose (p1@(mkBall Cr1 Bd1)) (p2@(mkBall Cr2 Bd2)) = mkBall carrier bound where
   open Ball

   two' : Set
   two' = Pushout (c0 .Bd) (c0 .Bd) -- pushout of two copies of ! : 0 → 1

   carrier : Set
   carrier = (Pushout (λ (_ : Unit) → cod p1) (λ (_ : Unit) → dom p2))

   bound : two' → carrier
   bound (inl _) = inl (dom p1)
   bound (inr _) = inr (cod p2)
