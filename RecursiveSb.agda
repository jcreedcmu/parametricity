{-# OPTIONS --cubical --rewriting  #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module RecursiveSb where

record Bundle : Setω where
 field
  F : {ℓ : Level} → Set ℓ → Set ℓ
  η : {ℓ : Level} {A : Set ℓ} → A → F A
  G : {ℓ : Level} → F (Set ℓ) → Set ℓ
  p : {ℓ : Level} → (x : Set ℓ) → G (η x) ≡p x


-- record Bundle : Setω where
--  field
--   η : {ℓ : Level} {A : Set ℓ} → A → G (η A)
--   G : {ℓ : Level} → G (η (Set ℓ)) → Set ℓ
