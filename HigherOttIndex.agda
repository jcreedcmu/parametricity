{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
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

module HigherOttIndex where

postulate
 S : Set

gl : ∀ {ℓ} (A : S → Set ℓ) → Set ℓ
gl A = (s : S) → A s

postulate
 -- morally, push ∂ f b ≈ (a : A) × (∂ a) × f a ≡ b
 -- define by induction on B, then f?
 push : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ'} {B : Set ℓ} → (A → Set ℓ'') → (A → B) → (B → Set ℓ'')

 -- define by induction on B
 Bd : ∀ {ℓ ℓ'} (B : Set ℓ) → (B → Set ℓ') → Set ℓ

 -- define by induction on f
 ap : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (∂ : A → Set ℓ'')
        (f : A → B) (p : Bd A ∂) → Bd B (push ∂ f)

 Bd/U : ∀ {ℓ} {∂ : Set ℓ → Set ℓ} → Bd (Set ℓ) ∂ ≡p (((A : Set ℓ) → ∂ A → A) → Set ℓ)
 {-# REWRITE Bd/U #-}

 Bd/× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p : A × B → Set (ℓ ⊔ ℓ')} → Bd (A × B) p ≡p
      Bd A (push p fst) × Bd B (push p snd)
 {-# REWRITE Bd/× #-}
{-
 Bd/→ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : S → A → B} → Bd S (A → B) f ≡p
      ({a : S → A} → Bd S A a → Bd S B (λ s → f s (a s)))

-}

 Bd/→ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f∂ : (A → B) → Set (ℓ ⊔ ℓ')} → Bd (A → B) f∂ ≡p
       ( {a : (f : A → B) → f∂ f → A} → Bd A {!!} → Bd B {!!} )
--       ({a : S → A} → Bd A a → Bd B (λ s → f s (a s)))
--  {-# REWRITE Bd/→ #-}

-- Bdd : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') {a : S → A} → Bd A a → gl (B ∘ a) → Set ℓ'
-- Bdd B p ba = ap B p ba

-- postulate
--  ap/→ : ∀ {ℓ0 ℓ ℓ'} {X : Set ℓ0} {A : X → Set ℓ} {B : X → Set ℓ'}
--              (x : S → X) (x~ : Bd X x)
--              {f : (s : S) → (a : A (x s)) → B (x s) }
--       → ap (λ x → A x → B x) x~ f ≡p ({a : gl (A ∘ x)} → ap A x~ a → ap B x~ λ s → f s (a s))
--  -- {-# REWRITE Bdd/→ #-} -- can't make this a rewrite rule, as I'm effectively trying to do HOAS!

--  Bd/Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f : S → (a : A) → B a} → Bd ((a : A) → B a) f ≡p
--       ({a : S → A} (p : Bd A a) → Bdd B p (λ s → f s (a s)) )
--  {-# REWRITE Bd/Π #-}

-- postulate
--  apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a : S → A} (f : (a : A) → B a) (p : Bd A a) → Bdd B p (f ∘ a)

--  ap/id : ∀ {ℓ} {A : S → Set ℓ} {R : gl A → Set ℓ} →
--         ap {a = A} (λ X → X) R ≡p R
--  {-# REWRITE ap/id #-}

-- foo : {A : S → Set} (id : (X : Set) → X → X) (R : gl A → Set)
--       → ap (λ z → z → z) R (λ s → id (A s))
-- foo id R = apd id R

-- foo-step : (A : S → Set) {id : (X : Set) → X → X} (R : gl A → Set)
--     → ap (λ z → z → z) R (id ∘ A) ≡p ({a : gl A} → R a → R (λ s → id (A s) (a s)))
-- foo-step A R = ap/→ A R
