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

   record Atotal : Set ℓ where
    constructor tea
    field
     at : T
     ae : E at
     aa : A ae

   ff : Σ T E × R → T × R
   ff ((t , e) , r) = t , r
   gg : Σ T E × R → Atotal
   gg ((t , e) , r) = tea t e (f r e)

   PGel : Set ℓ
   PGel = Push {A = T × R} {B = Atotal} {C = Σ T E × R} ff gg

   PGelPushMap = {!pushMap ff gg!}

   GelIsPGel : Σ T Gel ≅ PGel
   GelIsPGel = isoToEquiv (iso GelPGel PGelGel {!!} {!!}) where
     GelPGel : Σ T Gel → PGel
     GelPGel (t , gstrand r) = pinl (t , r)
     GelPGel (t , gpoint {e} a) = pinr (tea t e a)
     GelPGel (t , gpath {e} r i) = ppath ((t , e) , r) i

     PGelGel : PGel → Σ T Gel
     PGelGel (pinl (t , r)) = (t , gstrand r)
     PGelGel (pinr (tea t e a)) = (t , gpoint {e = e} a)
     PGelGel (ppath ((t , e) , r) i) = (t , gpath {e = e} r i)

   PGelπ : PGel → T
   PGelπ (pinl (t , r)) = t
   PGelπ (pinr (tea t e a)) = t
   PGelπ (ppath ((t , e) , r) i) = t

   -- module _ (t : T) (f : Σ T E × R → T × R) (g : (E t) × R → T → Σ (E t) A)
   --          where
   --   PGelPushMap : (p : Push f g) (d : T) → Push (λ c → f c d) (λ c → g c d)
   --   PGelPushMap p = pushMap f g p

   --   PGelCommute : isEquiv PGelPushMap
   --   PGelCommute = ▻Commute f g

   -- module _ (g : (t : T) → Gel t) where

   --   ungel : R
   --   ungel = {!GelIsPushout t!}
