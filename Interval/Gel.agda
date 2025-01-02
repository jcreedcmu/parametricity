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
   GelIsPush t = isoToEquiv (iso fore back sect retr) where
     fore : Gel t → Push (ff {t}) gg
     fore (gstrand r) = pinl r
     fore (gpoint {e} a) = pinr (e , a)
     fore (gpath {e} r i) = ppath (e , r) i

     back : Push (ff {t}) gg → Gel t
     back (pinl r) = (gstrand r)
     back (pinr (e , a)) = (gpoint {e = e} a)
     back (ppath (e , r) i) = (gpath {e = e} r i)

     sect : (x : Push (ff {t}) gg) → fore (back x) ≡ x
     sect (pinl a) i = pinl a
     sect (pinr b) i = pinr b
     sect (ppath (c1 , c2) i) j = (ppath (c1 , c2) i)

     retr : (x : Gel t) → back (fore x) ≡ x
     retr (gstrand r) i = gstrand r
     retr (gpoint a) i = gpoint a
     retr (gpath {e} r i) j = gpath {e = e} r i

   module _ (isDiscrete : isEquiv (λ (r : R) (t : T) → r)) where

     extract-r : Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg) → R
     extract-r (pinl a) = invIsEq isDiscrete a
     extract-r (pinr b) = abort (EndNonSurj (fst ∘ b))
     extract-r (ppath c i) = abort {A = pA} contra i where
           contra = EndNonSurj (fst ∘ gg ∘ c)
           pA = abort contra ≡ isDiscrete .equiv-proof (ff ∘ c) .fst .fst

     gel : R → (t : T) → Gel t
     gel r t = gstrand {t} r

     ungel : (g : (t : T) → Gel t) → R
     ungel g = extract-r (invIsEq (▻DepCommute ff gg) (λ t → funIsEq (GelIsPush t .snd) (g t)))

     gelβ : (g : (t : T) → Gel t) → gel (ungel g) ≡ g
     gelβ g i t = {!!}

     gelη : (r : R) → ungel (gel r) ≡ r
     gelη r = (cong extract-r (retIsEq (▻DepCommute ff gg) (pinl (λ t → r)))) ∙ (retIsEq isDiscrete r)
