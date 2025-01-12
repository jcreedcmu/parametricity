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

-- Some useful isomorphic transformations of Gel

module Interval.GelIso where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

  disc : ∀ {ℓ0} → Set ℓ0 → Set (ℓ ⊔ ℓ0)
  disc A = bridgeDiscrete T A

 -- we can do the relation as indexed instead of fibered
 module IndexedRelMod
       {A : {t : T} (e : E t) → Set ℓ}
       (R : (aa : {t : T} (e : E t) → A e) → Set ℓ)
       where

   Rtotal : Set ℓ
   Rtotal = (Σ ({t : T} (e : E t) → A e) R)

   ftotal : (r : Rtotal) {t : T} (e : E t) → A e
   ftotal (a , r) e = a e

   module Prev = Interval.Gel.main D S Rtotal ftotal

   data Gel (t : T) : Set ℓ where
        gstrand : (aa : {t : T} (e : E t) → A e) (r : R aa) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (aa : {t : T} (e : E t) → A e) (r : R aa)
                → gpoint (aa e) ≡ gstrand aa r

   thm : (t : T) → Prev.Gel t ≅ Gel t
   thm t = isoToEquiv (iso fore back sect retr) where
    open Prev using (gstrand ; gpoint ; gpath)
    fore : Prev.Gel t → Gel t
    fore (gstrand r) = gstrand (r .fst) (r .snd)
    fore (gpoint a) = gpoint a
    fore (gpath {e} r i) = gpath {e = e} (r .fst) (r .snd) i

    back : Gel t → Prev.Gel t
    back (gstrand aa r) = gstrand (aa , r)
    back (gpoint a) = gpoint a
    back (gpath {e} aa r i) = gpath {e = e} (aa , r) i

    sect : (g : Gel t) → fore (back g) ≡ g
    sect (gstrand aa r) i = gstrand aa r
    sect (gpoint a) i = gpoint a
    sect (gpath {e} aa r i) j = gpath {e = e} aa r i

    retr : (g : Prev.Gel t) → back (fore g) ≡ g
    retr (gstrand r) i = gstrand r
    retr (gpoint a) i = gpoint a
    retr (gpath{e} r i) j = gpath {e = e} r i

 -- lump together the t and E t arguments into a sigma
 module LumpTogetherMod
      {A : Σ T E → Set ℓ}
      (R : (aa : (s : Σ T E) → A s) → Set ℓ)
      where

   Agen : {t : T} (e : E t) → Set ℓ
   Agen {t} e = A (t , e)

   Rgen : ({t : T} (e : E t) → Agen e) → Set ℓ
   Rgen aa = R (λ s → aa (s .snd))

   module Prev = IndexedRelMod Rgen

   data Gel : T → Set ℓ where
        gstrand : {t : T} (aa : (s : Σ T E) → A s) (r : R aa) → Gel t
        gpoint : {s : Σ T E} (a : A s) → Gel (s .fst)
        gpath : {s : Σ T E} (aa : (s : Σ T E) → A s) (r : R aa) → gpoint (aa s) ≡ gstrand aa r
   thm : (t : T) → Prev.Gel t ≅ Gel t
   thm t = isoToEquiv (iso fore back sect retr) where
    open Prev using (gstrand ; gpoint ; gpath)
    fore : Prev.Gel t → Gel t
    fore (gstrand aa r) = gstrand (λ s → aa (s .snd)) r
    fore (gpoint a) = gpoint a
    fore (gpath {e} aa r i) = gpath {s = (t , e)} (λ s → aa (s .snd)) r i

    back : Gel t → Prev.Gel t
    back (gstrand aa r) = gstrand (λ {t} e → aa (t , e)) r
    back (gpoint {t , e} a) = gpoint {e = e} a
    back (gpath {t , e} aa r i) = gpath {e = e} (λ {t} e → aa (t , e)) r i

    sect : (g : Gel t) → fore (back g) ≡ g
    sect (gstrand aa r) i = gstrand aa r
    sect (gpoint a) i = gpoint a
    sect (gpath {s} aa r i) j = gpath {s = s} aa r i

    retr : (g : Prev.Gel t) → back (fore g) ≡ g
    retr (gstrand aa r) i = gstrand aa r
    retr (gpoint a) i = gpoint a
    retr (gpath {e} aa r i) j = gpath {e = e} aa r i
