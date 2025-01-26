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

data Unit {ℓ : Level} : Type ℓ  where
 ⋆ : Unit


data Tele (ℓ : Level) : Type (lsuc ℓ)
⟦_⟧ : ∀ {ℓ} → Tele ℓ → Type ℓ

data Tele ℓ where
 tnil : Tele ℓ
 tcons : (t : Tele ℓ) (A : ⟦ t ⟧ → Type ℓ) → Tele ℓ

⟦ tnil ⟧ = Unit
⟦ tcons t A ⟧ = Σ[ g ∈ ⟦ t ⟧ ] A g

record Dapp : Typeω where
 field
  F : {ℓ : Level} → Type ℓ → Type ℓ
  _·_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → F (A → B) → F A → F B
  ⟪_,_⟫ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → F A → F B → F (A × B)
  η : {ℓ : Level} {A : Type ℓ} → A → F A

  Fd : {ℓ : Level} → F (Type ℓ) → Type ℓ
  _·d_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (f : F ((x : A) → B x)) (x : F A) → Fd (η B · x)
  d⟪_,_⟫ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → (a : F A) → Fd (η B · a) → F (Σ A B)

module _ (dapp : Dapp) where
 open Dapp dapp

 fmap : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → F A → F B
 fmap f x = η f · x

 dfst : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → F (Σ A B) → F A
 dfst = fmap fst

 dmap : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → B x) → (a : F A) → Fd (η B · a)
 dmap f x = η f ·d x

 dsnd : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → (M : F (Σ A B)) → Fd (η (B ∘ fst) · M)
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

--- Define some operations that generalize F, η to include substitutions

module Substs (D : Dapp) {ℓ : Level} {t : Tele ℓ} where
 open Dapp D
 ρ/ : (θ : F ⟦ t ⟧) (A : ⟦ t ⟧ → Type ℓ) → F (Type ℓ)
 F/ : (θ : F ⟦ t ⟧) (A : ⟦ t ⟧ → Type ℓ) → Type ℓ
 η/ : (θ : F ⟦ t ⟧) {A : ⟦ t ⟧ → Type ℓ} (M : (g : ⟦ t ⟧) → A g) → F/ θ A

 ρ/ θ A = η A · θ
 F/ θ A = Fd (ρ/ θ A)
 η/ θ M = η M ·d θ

-- Define how to extend F'ed substitutions incrementally
module _ (D : Dapp) {ℓ : Level}  where
 open Dapp D
 open Substs D

 extend : {t : Tele ℓ} (θ : F ⟦ t ⟧) {A : ⟦ t ⟧ → Type ℓ} (M : F/ θ A) → F ⟦ tcons t A ⟧
 extend θ M = d⟪ θ , M ⟫

postulate
 dlift : Dapp → Dapp

module _ {D : Dapp} where
 open Dapp D
 open Dapp (dlift D) using () renaming (F to Fbar ; η to ηbar ; Fd to Fdbar)
 postulate
  ∂ : ∀ {ℓ} {A : Type ℓ} → Fbar A → F A
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


pthm : (id : (X : Type) → X → X) (A B : Type) (R : A × B → Type) (a : A) (b : B) (r : R (a , b)) → R (id A a , id B b)
pthm id A B R a b r = {!fibIn (ηbar id)!} where
 open Dapp binary
 open Dapp (dlift binary) using () renaming (F to Fbar ; η to ηbar)
