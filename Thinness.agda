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
 isFull1 : {A : Set} {a a' : A} → (a ⇒ a') → Set -- is a prop
 isFull2 : {A : Set} {a a' : A} {f f' : a ⇒ a'} → (f ⇒ f') → Set -- is a prop

Ball0 : (A : Set) → Set
Ball0 A = A

Sphere0 : (A : Set) → Set
Sphere0 A = A × A

Ball1 : (A : Set) (s0 : Sphere0 A) → Set
Ball1 A (src , tgt) = src ⇒ tgt

Sphere1 : (A : Set) (s0 : Sphere0 A) → Set
Sphere1 A s0 = Ball1 A s0 × Ball1 A s0

Ball2 : (A : Set) (s0 : Sphere0 A) (s1 : Sphere1 A s0) → Set
Ball2 A s0 (src , tgt) = src ⇒ tgt

Sphere2 : (A : Set) (s0 : Sphere0 A) (s1 : Sphere1 A s0) → Set
Sphere2 A s0 s1 = Ball2 A s0 s1 × Ball2 A s0 s1

module _ (A : Set) where
 data Tele : (n : ℕ) → Set
 Ball : {n : ℕ} → Tele n → Set
 Sphere : {n : ℕ} → Tele n → Set

 data Tele where
  tnil : Tele zero
  tcons : {n : ℕ} (t : Tele n) (s : Sphere t) → Tele (suc n)
 Sphere t = Ball t × Ball t
 Ball tnil = A
 Ball (tcons t (src , tgt)) = src ⇒ tgt

record GoodEdge : Set₁ where constructor mkGoodEdge ; field
 A : Set
 bd : two → A
 path : bd t0 ⇒ bd t1
 full : isFull1 path

module _ (ge1 : two → GoodEdge) where
 postulate
  mergedSpace1 : Set
  mergedBd1 : two → mergedSpace1

 -- record GoodEdge2 : Set₁ where constructor mkGoodEdge2 ; field
 --  A : Set
 --  bd : {!!}
