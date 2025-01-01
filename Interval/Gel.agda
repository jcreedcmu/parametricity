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

 module _ {A : {t : T} (e : E t) → Set ℓ}  (f : (r : R) {t : T} (e : E t) → A e) where

   data Gel (t : T) : Set ℓ where
        gstrand : (r : R) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (r : R) → gpoint (f r e) ≡ gstrand r

   data TotalGel : Set ℓ where
        tstrand : (t : T) (r : R) → TotalGel
        tpoint : (t : T) (e : E t) (a : A e) → TotalGel
        tpath : (t : T) (e : E t) (r : R) → tpoint t e (f r e) ≡ tstrand t r

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

   PGelPushMap : Push (λ k → ff ∘ k) (λ k → gg ∘ k) → T → Push ff gg
   PGelPushMap = pushMap ff gg

   PGelCommute : isEquiv PGelPushMap
   PGelCommute = ▻Commute ff gg

   PGelLift : (T → Push ff gg) → Push (λ k → ff ∘ k) (λ k → gg ∘ k)
   PGelLift = invIsEq PGelCommute

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

   module _ (g : (t : T) → Gel t) where

     pg : T → PGel
     pg t = funIsEq (GelIsPGel .snd) (t , g t)

     thing : Push (_∘_ ff) (_∘_ gg)
     thing = PGelLift pg

     tgelOfGel : (t : T) → Gel t → TotalGel
     tgelOfGel t (gstrand r) = tstrand t r
     tgelOfGel t (gpoint a) = tpoint t _ a
     tgelOfGel t (gpath {e} r i) = tpath t e r i


     extract-r : Push (λ k (t : T) → ff (k t)) (_∘_ gg) → R
     extract-r (pinl a) = invIsEq ▻Discrete (λ (t : T) → proj₂ (a t))
     extract-r (pinr b) = {!pinr-lemma!}
     extract-r (ppath c i) = {!!}

     thing-r : R
     thing-r = extract-r thing
