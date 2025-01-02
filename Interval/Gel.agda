{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to abort)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base

-- Instead of postulating the Gel type, I'm trying to understand it as
-- defined by pushout of copies of the interval

module Interval.Gel where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

 module _ {A : {t : T} (e : E t) → Set ℓ1} (R : Set ℓ) (f : (r : R) {t : T} (e : E t) → A e) where

   data Gel (t : T) : Set ℓ where
        gstrand : (r : R) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (r : R) → gpoint (f r e) ≡ gstrand r

   ff : {t : T} → (E t) × R → R
   ff (e , r) = r

   gg : {t : T} →  (E t) × R → Σ (E t) A
   gg (e , r) = (e , f r e)

   GelIsPush : (t : T) → Gel t ≅ Push (ff {t}) gg
   GelIsPush = {!!}

   module _ (g : (t : T) → Gel t) (isDiscrete : isEquiv (λ (r : R) (t : T) → r)) where

     extract-r : Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg) → R
     extract-r (pinl a) = invIsEq isDiscrete a
     extract-r (pinr b) = abort (EndNonSurj (fst ∘ b))
     extract-r (ppath c i) = abort {A = pA} contra i where
           contra = EndNonSurj (fst ∘ gg ∘ c)
           pA = abort contra ≡ isDiscrete .equiv-proof (ff ∘ c) .fst .fst

     ungel : R
     ungel = extract-r (invIsEq (▻DepCommute ff gg) (λ t → funIsEq (GelIsPush t .snd) (g t)))
