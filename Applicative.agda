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

data Unit {ℓ : Level} : Set ℓ where
 * : Unit


-- module Telescopes where
--  data T (ℓ : Level) : ℕ → Set (ℓ-suc ℓ)
--  ⟦_⟧ : {ℓ : Level} {n : ℕ} → T ℓ n → Set ℓ
--  data T ℓ where
--   tnil : T ℓ zero
--   tcons : {n : ℕ} (t : T ℓ n) → (⟦ t ⟧ → Set ℓ) → T ℓ (suc n)
--  ⟦ tnil ⟧ = Unit
--  ⟦ tcons tl h ⟧ = Σ ⟦ tl ⟧ h

--  zip : ∀ {ℓ} {n} → T ℓ n → T ℓ n → T ℓ n
--  zipthm : ∀ {ℓ} {n} (t t' : T ℓ n) → ⟦ zip t t' ⟧ → ⟦ t ⟧ × ⟦ t' ⟧

--  zip tnil  tnil = tnil
--  zip (tcons t x) (tcons t' x') = tcons (zip t t') λ z → x (zipthm t t' z .fst) × x' (zipthm t t' z .snd)

--  zipthm tnil tnil * = * , *
--  zipthm (tcons t x) (tcons t' x') (z , p , p') = (zipthm t t' z .fst , p) , (zipthm t t' z .snd , p')

＠ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → ((A → B) × A) → B
＠ (f , x) = f x

module App where
 postulate
  F : {ℓ : Level} → Set ℓ → Set ℓ
  fmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A → B) → F A → F B
  η : {ℓ : Level} {A : Set ℓ} → A → F A
  Fd : {ℓ : Level} → F (Set ℓ) → Set ℓ
  ⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F A → F B → F (A × B)
  d⟪_,_⟫ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (N : F A) → Fd (fmap ＠  ⟪ η B , N ⟫) → F (Σ A B)

 _·_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F (A → B) → F A → F B
 f · x = fmap ＠ ⟪ f , x ⟫

 dfst : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → F (Σ A B) → F A
 dfst = fmap fst

 postulate
  dmap : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → ((x : A) → B x) → (a : F A) → Fd (η B · a)

 -- This doesn't work with definitionally with my first guess, which was
 -- ⋯ → Fd (η B · dfst M) because I'd need some reductions about consecutive fmaps…
 -- But that's fine, this definition works.
 dsnd : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → (M : F (Σ A B)) → Fd (η (B ∘ fst) · M)
 dsnd = dmap snd

 postulate
  ηd : {ℓ : Level} → (x : F (Set ℓ)) → Fd x




 -- (_·d_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → F ((x : A) → B x) → (a : F A) → Fd (η B · a))
