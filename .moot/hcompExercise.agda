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
open import Function.Base

module hcompExercise (A : Set) (a b c : A) (p : a ≡ b) (q : b ≡ c) where

pq : a ≡ c
pq x = hcomp (λ y → λ { (x = i0) → p (~ y) ; (x = i1) → q y }) b

z = inS
w = outS

pqSquare : Square (λ _ → b) pq (sym p) q
pqSquare y x = hfill (λ y → λ { (x = i0) → p (~ y) ; (x = i1) → q y }) (inS b) y
