{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
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

module HigherOttShape where

module _ (S : Set) where
 gl : ∀ {ℓ} (A : S → Set ℓ) → Set ℓ
 gl A = (s : S) → A s

 postulate
  Bd : ∀ {ℓ} (B : Set ℓ) → (S → B) → Set ℓ
  ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a : S → A} (f : A → B) (p : Bd A a) → Bd B (f ∘ a)

  Bd/U : ∀ {ℓ} {A : S → Set ℓ} → Bd (Set ℓ) A ≡p (gl A → Set ℓ)
  {-# REWRITE Bd/U #-}

  Bd/× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p : S → A × B} → Bd (A × B) p ≡p
       Bd A (λ s → fst (p s)) × Bd B (λ s → snd (p s))
  {-# REWRITE Bd/× #-}
  Bd/→ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : S → A → B} → Bd (A → B) f ≡p
       ({a : S → A} → Bd A a → Bd B (λ s → f s (a s)))
  {-# REWRITE Bd/→ #-}

 Bdd : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') {a : S → A} → Bd A a → gl (B ∘ a) → Set ℓ'
 Bdd B p ba = ap B p ba

 postulate
  ap/→ : ∀ {ℓ0 ℓ ℓ'} {X : Set ℓ0} {A : X → Set ℓ} {B : X → Set ℓ'}
              (x : S → X) (x~ : Bd X x)
              {f : (s : S) → (a : A (x s)) → B (x s) }
       → ap (λ x → A x → B x) x~ f ≡p ({a : gl (A ∘ x)} → ap A x~ a → ap B x~ λ s → f s (a s))
  -- {-# REWRITE Bdd/→ #-} -- can't make this a rewrite rule, as I'm effectively trying to do HOAS!

  Bd/Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f : S → (a : A) → B a} → Bd ((a : A) → B a) f ≡p
       ({a : S → A} (p : Bd A a) → Bdd B p (λ s → f s (a s)) )
  {-# REWRITE Bd/Π #-}

 postulate
  apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a : S → A} (f : (a : A) → B a) (p : Bd A a) → Bdd B p (f ∘ a)

  ap/id : ∀ {ℓ} {A : S → Set ℓ} {R : gl A → Set ℓ} →
         ap {a = A} (λ X → X) R ≡p R
  {-# REWRITE ap/id #-}

 foo : {A : S → Set} (id : (X : Set) → X → X) (R : gl A → Set)
       → ap (λ z → z → z) R (λ s → id (A s))
 foo id R = apd id R

 foo-step : (A : S → Set) {id : (X : Set) → X → X} (R : gl A → Set)
     → ap (λ z → z → z) R (id ∘ A) ≡p ({a : gl A} → R a → R (λ s → id (A s) (a s)))
 foo-step A R = ap/→ A R

module _ where
 postulate
  isDiag : ∀ {ℓ ℓ'} {B : Set ℓ} (b : B) → Bd Unit B (λ _ → b) → Set ℓ' -- sketchy universe level stuff going on here

  isDiag/U : ∀ {ℓ}  (A : Set ℓ) (d : Bd Unit (Set ℓ) (λ _ → A)) → isDiag A d ≡p ((a : A) → isContr (d (λ _ → a)))
  {-# REWRITE isDiag/U #-}

  funcS : ∀ {ℓ} {S S' : Set} (f : S' → S) {B : Set ℓ} (b : S → B) → Bd S B b → Bd S' B (b ∘ f)

  funcS/U : ∀ {ℓ} {S S' : Set} (f : S' → S) (A : S → Set ℓ) (d : Bd S (Set ℓ) A) → funcS f A d ≡p λ x' → {!Σ!}
