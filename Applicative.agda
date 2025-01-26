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

data Unit {ℓ : Level} : Type ℓ where
 ⋆ : Unit

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

binary : Dapp
binary = record
          { F = λ A → A × A
          ; _·_ = λ fs xs → (fst fs) (fst xs) , (snd fs) (snd xs)
          ; ⟪_,_⟫ = λ as bs → (fst as , fst bs) , (snd as , snd bs)
          ; η = λ a → (a , a)
          ; Fd = λ A → (fst A) × (snd A)
          ; _·d_ = λ fs xs → (fst fs) (fst xs) , (snd fs) (snd xs)
          ; d⟪_,_⟫ = λ as bs → (fst as , fst bs) , (snd as , snd bs)
          }

postulate
 dlift : Dapp → Dapp

module _ {D : Dapp} where
 open Dapp D
 open Dapp (dlift D) using () renaming (F to Fbar ; η to ηbar ; Fd to Fdbar)
 postulate
  ∂ : ∀ {ℓ} {A : Set ℓ} → Fbar A → F A
  fib : ∀ {ℓ} (A : Type ℓ) (x : F A) → Type ℓ
  getBar : ∀ {ℓ} {A : Type ℓ} {x : F A} → fib _ x → Fbar A
  fibIn : ∀ {ℓ} {A : Type ℓ} (abar : Fbar A) → fib _ (∂ abar)

  getBarIn : ∀ {ℓ} {A : Type ℓ} (abar : Fbar A) → getBar (fibIn abar) ≡p abar
  {-# REWRITE getBarIn #-}

  ∂GetBar : ∀ {ℓ} {A : Type ℓ} (b : F A) (ϕ : fib _ b) → ∂ (getBar ϕ) ≡p b
  {-# REWRITE ∂GetBar #-}

  ∂η : ∀ {ℓ} {A : Type ℓ} (a : A) → ∂ {A = A} (ηbar a) ≡p (η a)
  {-# REWRITE ∂η #-}

  -- stub : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (x : F ((x : A) → B x)) → fib ((x : A) → B x) x ≡p Unit
  -- {-# REWRITE stub #-}

  star : (id : F ((X : Type) → X → X)) (FX : F Type) (Fx : Fd FX) → Fd FX

  stub : (id : F ((X : Type) → X → X)) → fib ((X : Type) → X → X) id ≡p ((X : Fbar Type) (x : Fdbar X) → fib {!!} {!star id (∂ X) (∂ x)!})
  {-# REWRITE stub #-}


pthm : (id : (X : Type) → X → X) (A B : Set) (R : A × B → Set) (a : A) (b : B) (r : R (a , b)) → R (id A a , id B b)
pthm id A B R a b r = {!fibIn (ηbar id)!} where
 open Dapp binary
 open Dapp (dlift binary) using () renaming (F to Fbar ; η to ηbar)
