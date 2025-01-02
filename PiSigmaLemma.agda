{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

Π : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Π A B = (x : A) → B x

ΠΣ-lemma : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} →
           Π A B ≅ (Σ[ f ∈ (A → Σ A B) ] ((a : A) → f a .fst ≡ a))
ΠΣ-lemma = {!!}
