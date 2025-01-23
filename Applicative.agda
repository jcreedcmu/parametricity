{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
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

module Applicative where
postulate
 F : {ℓ : Level} → Set ℓ → Set ℓ
 _·_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F (A → B) → F A → F B
 ⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F A → F B → F (A × B)
 η : {ℓ : Level} {A : Set ℓ} → A → F A

 Fd : {ℓ : Level} → F (Set ℓ) → Set ℓ
 _·d_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} (f : F ((x : A) → B x)) (x : F A) → Fd (η B · x)
 d⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (a : F A) → Fd (η B · a) → F (Σ A B)

fmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A → B) → F A → F B
fmap f x = η f · x

dfst : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → F (Σ A B) → F A
dfst = fmap fst

dmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → ((x : A) → B x) → (a : F A) → Fd (η B · a)
dmap f x = η f ·d x

dsnd : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (M : F (Σ A B)) → Fd (η (B ∘ fst) · M)
dsnd M = η snd ·d M
