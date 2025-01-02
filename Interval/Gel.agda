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

 -- module _ {A : Set ℓ} (R : Set ℓ) (ra : (r : R) {t : T} (e : E t) → A) (at : A → T)
 --          (ae : (a : A) → E (at a)) (rae : (r : R) {t : T} (e : E t) → at (ra r {t} e) ≡ t)
 --          where

 --   data Gel (t : T) : Set ℓ where
 --        gstrand : (r : R) → Gel t
 --        gpoint : (a : A) → Gel t
 --        gpath : (r : R) {t : T} (e : E t) → gpoint (ra r e) ≡ gstrand r

 R = D -- we want the relation to be bridge-discrete, so choose it to be
       -- the direction of the interval

 module _ {A : {t : T} (e : E t) → Set ℓ1}  (f : (r : R) {t : T} (e : E t) → A e) where

   data Gel (t : T) : Set ℓ where
        gstrand : (r : R) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (r : R) → gpoint (f r e) ≡ gstrand r

   PA : T → Set ℓ1
   PA t = R

   PB : T → Set ℓ
   PB t = Σ (E t) A

   PC : T → Set ℓ
   PC t = (E t) × R

   ff : {t : T} → PC t → PA t
   ff (e , r) = r

   gg : {t : T} → PC t → PB t
   gg (e , r) = (e , f r e)

   PGel : T → Set ℓ
   PGel t = Push (ff {t}) gg

   PGelPushMap : Push (λ k t' → ff (k t')) (λ k t' → gg (k t')) → (t : T) → Push (ff {t}) gg
   PGelPushMap = depPushMap ff gg

   PGelCommute : isEquiv PGelPushMap
   PGelCommute = ▻DepCommute ff gg

   PGelLift : ((t : T) → Push ff gg) → Push (λ k t' → ff (k t')) (_∘_ gg)
   PGelLift = invIsEq PGelCommute

   GelIsPGel : (t : T) → Gel t ≅ PGel t
   GelIsPGel = {!!}

   module _ (g : (t : T) → Gel t) where

     extract-r : Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg) → R
     extract-r (pinl a) = invIsEq ▻Discrete a
     extract-r (pinr b) = abort (EndNonSurj (fst ∘ b))
     extract-r (ppath c i) = abort {A = pA} contra i where
           contra = EndNonSurj (fst ∘ gg ∘ c)
           pA = abort contra ≡ ▻Discrete .equiv-proof (ff ∘ c) .fst .fst

     thing-r : R
     thing-r = extract-r (PGelLift (λ t → funIsEq (GelIsPGel t .snd) (g t)))
