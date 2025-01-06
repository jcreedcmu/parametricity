{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base
import Interval.Gel

{-
 - There remains some stuff to be formulated and proved here.
 - Something like: a homomorphism between relations R1 and R2 is the same
 - thing as a map (t : T) → Gel R1 t → Gel R2 t
 -}
module Interval.Functoriality where

module _ {ℓ : Level} (D : Set ℓ) (S : Set ℓ) where
 private
  T = D ▻ S
  E = End

  module toOpen0 = Interval.Gel.main {ℓ} {ℓ} D S
  open toOpen0

  module _ {A1 : {t : T} (e : E t) → Set ℓ}
           {A2 : {t : T} (e : E t) → Set ℓ}
           (R1 R2 : Set ℓ)
           (disc-R2 : disc R2)
           (disc-EA2 : (t : T) → disc (Σ (E t) A2))
           (disc-ER2 : (t : T) → disc (E t × R2))
           (disc-R1 : disc R1)
           (disc-EA1 : (t : T) → disc (Σ (E t) A1))
           (disc-ER1 : (t : T) → disc (E t × R1))
           (f1 : (r : R1) {t : T} (e : E t) → A1 e)
           (f2 : (r : R2) {t : T} (e : E t) → A2 e)
           (ah : {t : T} (e : E t) → A1 e → A2 e)
    where

    module toOpen1 = Interval.Gel.main.gel {ℓ} {ℓ} D S R1 f1
    open toOpen1 renaming (Gel to Gel1 ; gstrand to gstrand1 ; gpoint to gpoint1 ; gpath to gpath1 ; gel to gel1 )
    module toOpen2 = Interval.Gel.main.gel {ℓ} {ℓ} D S R2 f2
    open toOpen2 renaming (Gel to Gel2 ; gstrand to gstrand2 ; gpoint to gpoint2 ; gpath to gpath2 ; gel to gel2 )

    ungel1 : ((t : T) → Gel1 t) → R1
    ungel1 = toOpen1.ungel disc-R1 disc-EA1 disc-ER1

    ungel2 : ((t : T) → Gel2 t) → R2
    ungel2 = toOpen2.ungel disc-R2 disc-EA2 disc-ER2

    record Bundle (t : T) : Set ℓ where
     field
      coarseMap : R1 → Gel2 t
      boundaryMap : (e : E t) (a1 : A1 e) → Gel2 t
      compat : (e : E t) (r1 : R1) → boundaryMap e (f1 r1 e) ≡ coarseMap r1

    module ≅1 (t : T) where
     open Bundle
     open Interval.Gel.main.gel

     fore : (Gel1 t → Gel2 t) → Bundle t
     fore uniform = record {
         coarseMap = λ r1 → uniform (gstrand r1) ;
         boundaryMap = λ e a1 → uniform (gpoint a1) ;
         compat = λ e r1 i → uniform (gpath {e = e} r1 i)
         }

     back : Bundle t → (Gel1 t → Gel2 t)
     back b (gstrand r1) = b .coarseMap r1
     back b (gpoint {e} a1) = b .boundaryMap e a1
     back b (gpath {e} r1 i) = b .compat e r1 i

     sect : (b : Bundle t) → fore (back b) ≡ b
     sect b i = b

     retr : (u : Gel1 t → Gel2 t) → back (fore u) ≡ u
     retr u i (gstrand r) = u (gstrand r)
     retr u i (gpoint a) = u (gpoint a)
     retr u i (gpath {e} r j) = u (gpath {e = e} r j)

     thm : (Gel1 t → Gel2 t) ≅ Bundle t
     thm = isoToEquiv (iso fore back sect retr)

    record Bundle2 : Set ℓ where
     field
      coarseMap : R1 → (t : T) → Gel2 t
      boundaryMap : (t : T) (e : E t) (a1 : A1 e) → Gel2 t
      compat : (t : T) (e : E t) (r1 : R1) → boundaryMap t e (f1 r1 e) ≡ coarseMap r1 t

    module ≅2 where
     open Interval.Gel.main.gel

     fore : ((t : T) → Bundle t) → Bundle2
     fore tb = record {
       coarseMap = λ r1 t → tb t .Bundle.coarseMap r1 ;
       boundaryMap = λ t e a1 → tb t .Bundle.boundaryMap e a1 ;
       compat = λ t e r1 i → tb t .Bundle.compat e r1 i
       }

     back : Bundle2 → ((t : T) → Bundle t)
     back b2 t = record {
       coarseMap = λ r1 → b2 .Bundle2.coarseMap r1 t ;
       boundaryMap = λ e a1 → b2 .Bundle2.boundaryMap t e a1 ;
       compat = λ e r1 i → b2 .Bundle2.compat t e r1 i
       }

     thm : ((t : T) → Bundle t) ≅ Bundle2
     thm = isoToEquiv (iso fore back (λ b i → b) (λ u i → u))

    cvtR2 : R2 → (t : T) → Gel2 t
    cvtR2 r2 t = Gel2.gstrand r2

    cvtA2 : {t : T} (e : E t) → A2 e → Gel2 t
    cvtA2 e a2 = Gel2.gpoint a2

    postulate
      ≅R2 : isEquiv cvtR2
      ≅A2 : {t : T} (e : E t) → isEquiv (cvtA2 e)

    -- Relative to Bundle2 we've just changed coarseMap's type
    record Bundle3 : Set ℓ where
     field
      coarseMap : R1 → R2
      boundaryMap : (t : T) (e : E t) (a1 : A1 e) → Gel2 t
      compat : (t : T) (e : E t) (r1 : R1) → boundaryMap t e (f1 r1 e) ≡ cvtR2 (coarseMap r1) t

    module ≅3 where
     open Interval.Gel.main.gel

     fore : Bundle2 → Bundle3
     fore b2 = record {
       coarseMap = λ r1 → invIsEq ≅R2 (b2 .Bundle2.coarseMap r1) ;
       boundaryMap = b2 .Bundle2.boundaryMap ;
       compat = λ t e r1 → {!!}
       }

     back : Bundle3 → Bundle2
     back b3 = record {
       coarseMap = λ r1 t → gstrand (b3 .Bundle3.coarseMap r1) ;
       boundaryMap = b3 .Bundle3.boundaryMap ;
       compat = b3 .Bundle3.compat
       }

     thm : Bundle2 ≅ Bundle3
     thm = isoToEquiv (iso fore back {!!} {!!})
