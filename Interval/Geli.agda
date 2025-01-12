{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
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
open import Function.Base
import Interval.Gel

-- Gel, but R is indexed instead of fibered

module Interval.Geli where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

  disc : ∀ {ℓ0} → Set ℓ0 → Set (ℓ ⊔ ℓ0)
  disc A = bridgeDiscrete T A

 module maini {A : {t : T} (e : E t) → Set ℓ} (R : (aa : {t : T} (e : E t) → A e) → Set ℓ)  where

   Rtotal : Set ℓ
   Rtotal = (Σ ({t : T} (e : E t) → A e) R)

   ftotal : (r : Rtotal) {t : T} (e : E t) → A e
   ftotal (a , r) e = a e

   open Interval.Gel.main D S {A = A} Rtotal ftotal

   AR : Set ℓ
   AR = Σ ({t : T} (e : E t) → A e) R

   EAR : T → Set ℓ
   EAR t = E t × AR

   EA : T → Set ℓ
   EA t = Σ (E t) A

   data Geli (t : T) : Set ℓ where
        gstrandi : (aa : {t : T} (e : E t) → A e) (r : R aa) → Geli t -- AR
        gpointi : {e : E t} (a : A e) → Geli t -- EA
        gpathi : {e : E t} (aa : {t : T} (e : E t) → A e) (r : R aa) → gpointi (aa e) ≡ gstrandi aa r -- EAR

   thm : (t : T) → Gel t ≅ Geli t
   thm t = isoToEquiv (iso fore back sect retr) where
    fore : Gel t → Geli t
    fore (gstrand r) = gstrandi (r .fst) (r .snd)
    fore (gpoint a) = gpointi a
    fore (gpath {e} r i) = gpathi {e = e} (r .fst) (r .snd) i

    back : Geli t → Gel t
    back (gstrandi aa r) = gstrand (aa , r)
    back (gpointi a) = gpoint a
    back (gpathi {e} aa r i) = gpath {e = e} (aa , r) i

    sect : (g : Geli t) → fore (back g) ≡ g
    sect (gstrandi aa r) i = gstrandi aa r
    sect (gpointi a) i = gpointi a
    sect (gpathi {e} aa r i) j = gpathi {e = e} aa r i

    retr : (g : Gel t) → back (fore g) ≡ g
    retr (gstrand r) i = gstrand r
    retr (gpoint a) i = gpoint a
    retr (gpath{e} r i) j = gpath {e = e} r i
