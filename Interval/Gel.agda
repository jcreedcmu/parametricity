{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms

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

 module _ {A : {t : T} (e : E t) → Set ℓ} (R : Set ℓ) (f : (r : R) {t : T} (e : E t) → A e) where

   data Gel (t : T) : Set ℓ where
        gstrand : (r : R) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (r : R) → gpoint (f r e) ≡ gstrand r

   PGel : T → Set ℓ
   PGel t = Push {A = R} {B = Σ (E t) A} {C = (E t) × R} proj₂ λ {(e , r) → e , (f r e)}

   GelIsPushout : (t : T) → Gel t ≅ PGel t
   GelIsPushout t = isoToEquiv (iso fore back sect retr) where
     fore : Gel t → PGel t
     fore (gstrand r) = pinl r
     fore (gpoint {e} a) = pinr (e , a)
     fore (gpath {e} r i) = ppath (e , r) i

     back : PGel t → Gel t
     back (pinl r) = gstrand r
     back (pinr (e , a)) = gpoint {e = e} a
     back (ppath (e , r) i) = gpath {e = e} r i

     sect : (g : PGel t) → fore (back g) ≡ g
     sect (pinl a) _ = pinl a
     sect (pinr b) _ = pinr b
     sect (ppath (e , r) i) _ = ppath (e , r) i

     retr : (g : Gel t) → back (fore g) ≡ g
     retr (gstrand r) _ = gstrand r
     retr (gpoint a) _ = gpoint a
     retr (gpath {e} r i) _ = gpath {e = e} r i

   module _ (t : T)
            (f : (E t) × R → T → R) (g : (E t) × R → T → Σ (E t) A)
            where
     PGelPushMap : (p : Push f g) (d : T) → Push (λ c → f c d) (λ c → g c d)
     PGelPushMap p = pushMap f g p

     PGelCommute : isEquiv PGelPushMap
     PGelCommute = ▻Commute f g
