{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module Applicative where

data Unit {ℓ : Level} : Set ℓ where
 * : Unit

module _
 (F : {ℓ : Level} → Set ℓ → Set ℓ)
 (η : {ℓ : Level} {A : Set ℓ} → A → F A)
 (Fd : {ℓ : Level} → F (Set ℓ) → Set ℓ)
 (_·_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → F (A → B) → F A → F B)
 (_·d_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} → F ((x : A) → B x) → (a : F A) → Fd (η B · a))
 where

module Telescopes where
 data T (ℓ : Level) : ℕ → Set (ℓ-suc ℓ)
 ⟦_⟧ : {ℓ : Level} {n : ℕ} → T ℓ n → Set ℓ
 data T ℓ where
  tnil : T ℓ zero
  tcons : {n : ℕ} (t : T ℓ n) → (⟦ t ⟧ → Set ℓ) → T ℓ (suc n)
 ⟦ tnil ⟧ = Unit
 ⟦ tcons tl h ⟧ = Σ ⟦ tl ⟧ h

 zip : ∀ {ℓ} {n} → T ℓ n → T ℓ n → T ℓ n
 zipthm : ∀ {ℓ} {n} (t t' : T ℓ n) → ⟦ zip t t' ⟧ → ⟦ t ⟧ × ⟦ t' ⟧

 zip tnil  tnil = tnil
 zip (tcons t x) (tcons t' x') = tcons (zip t t') λ z → x (zipthm t t' z .fst) × x' (zipthm t t' z .snd)

 zipthm tnil tnil * = * , *
 zipthm (tcons t x) (tcons t' x') (z , p , p') = (zipthm t t' z .fst , p) , (zipthm t t' z .snd , p')
