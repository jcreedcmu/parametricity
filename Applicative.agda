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

record Dapp : Typeω where
 field
  F : {ℓ : Level} → Set ℓ → Set ℓ
  _·_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F (A → B) → F A → F B
  ⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F A → F B → F (A × B)
  η : {ℓ : Level} {A : Set ℓ} → A → F A

  Fd : {ℓ : Level} → F (Set ℓ) → Set ℓ
  _·d_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} (f : F ((x : A) → B x)) (x : F A) → Fd (η B · x)
  d⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (a : F A) → Fd (η B · a) → F (Σ A B)

module _ (dapp : Dapp) where
 open Dapp dapp

 fmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A → B) → F A → F B
 fmap f x = η f · x

 dfst : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → F (Σ A B) → F A
 dfst = fmap fst

 dmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → ((x : A) → B x) → (a : F A) → Fd (η B · a)
 dmap f x = η f ·d x

 dsnd : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (M : F (Σ A B)) → Fd (η (B ∘ fst) · M)
 dsnd M = η snd ·d M

nary : (S : Type) → Dapp
nary S = record
          { F = λ A → S → A
          ; _·_ = λ f x s → (f s) (x s)
          ; ⟪_,_⟫ = λ x1 x2 s → (x1 s) , (x2 s)
          ; η = λ a s → a
          ; Fd = λ A → (s : S) → A s
          ; _·d_ = λ f x s → (f s) (x s)
          ; d⟪_,_⟫ = λ x1 x2 s → (x1 s) , (x2 s)
          }

module _ where
 open Dapp
 postulate
  dlift : Dapp → Dapp
  ∂ : ∀ {ℓ} {D : Dapp} {A : Set ℓ} → dlift D .F A → D .F A

 postulate
  fib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b : B) → Type (ℓ ⊔ ℓ')
  getA : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} → fib f b → A
  fibIn : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) → fib f (f a)
  inGetA : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) → getA (fibIn f a) ≡p a
  {-# REWRITE inGetA #-}

  appA : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → A → B
  fGetA : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b : B) (ϕ : fib f b) → appA f (getA ϕ) ≡p b
  {-# REWRITE fGetA #-}

  appAapp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) → appA f a ≡p f a
  {-# REWRITE appAapp #-}
