{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

module Interval.Discreteness {ℓ : Level} (T : Set ℓ) where

-- bridgeDiscrete A := A has no T-cohesion
bridgeDiscrete : ∀ {ℓ0} (A : Set ℓ0)→ Set (ℓ ⊔ ℓ0)
bridgeDiscrete A = isEquiv (λ (a : A) (t : T) → a)
