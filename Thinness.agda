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

data Unit : Set where
 ⋆ : Unit

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
 isFull : {A : Set} (t : Tele A) (b : Ball A t) → Set -- is a prop

-- Ball0 : Set
-- Ball0 = Unit

-- Sphere0 : Set
-- Sphere0 = Unit

-- record Ball1 : Set₁ where field
--  A : Set
--  a0 a1 : A
--  path : a0 ⇒ a1
--  full : isFull (tcons tnil a0 a1) path

-- Sphere1 : Set₁
-- Sphere1 = Ball1 × Ball1

-- record Ball2 (s1 : Sphere1) : Set₁ where field
--  A : Set
--  a0 a1 : A
--  path : a0 ⇒ a1
--  full : isFull (tcons tnil a0 a1) path

record GoodEdge1 : Set₁ where constructor mkGoodEdge ; field
 A : Set
 a0 a1 : A
 path : a0 ⇒ a1
 full : isFull (tcons tnil a0 a1) path

postulate
 cell1 : GoodEdge1

module _ (ge1 : two → GoodEdge1) where
 postulate
  merged1 : Set -- pushout of ge1

 record GoodEdge2 : Set₁ where constructor mkGoodEdge2 ; field
  A : Set
  a0 a1 : A
  p0 p1 : a0 ⇒ a1
  path : p0 ⇒ p1
  full : isFull (tcons (tcons tnil a0 a1) p0 p1) path

 postulate
  cell2 : GoodEdge2
  bd2 : merged1 → cell2 .GoodEdge2.A
