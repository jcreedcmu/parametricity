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
open import Interval.ThreePush
import Interval.Endpoints
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

    Bundle0 : Set ℓ
    Bundle0 = Threep
       (R1 → (t : T) → Gel2 t)
       ((t : T) (e : E t) (a1 : A1 e) → Gel2 t)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → bm t e (f1 r1 e) ≡ cm r1 t)

    -- The first move is mainly to just use the pushout UMP to understand
    -- that, for each t, a map Gel1 t → ⋯ is the same thing as a pair of maps
    -- (g : R1) → ⋯
    -- (e : E t) (a1 : A1 e) → ⋯
    -- that are suitably compatible at endpoints. Therefore a uniform map
    -- (t : T) → Gel1 t → ⋯
    -- is the same thing as a compatible pair of maps
    -- (t : T) (g : R1) → ⋯
    -- (t : T) (e : E t) (a1 : A1 e) → ⋯
    -- In passing, we also commute the t-binder to the right of R1, which
    -- we'll need for future steps.
    module ≅0 (t : T) where
     open Interval.Gel.main.gel
     open Threep

     fore : ((t : T) → Gel1 t → Gel2 t) → Bundle0
     fore uniform = record {
         fa = λ r1 t → uniform t (gstrand r1) ;
         fb = λ t e a1 → uniform t (gpoint a1) ;
         fc = λ t e r1 i → uniform t (gpath {e = e} r1 i)
         }
     back : Bundle0 → (t : T) → (Gel1 t → Gel2 t)
     back b t (gstrand r1) = b .fa r1 t
     back b t (gpoint {e} a1) = b .fb t e a1
     back b t (gpath {e} r1 i) = b .fc t e r1 i

     sect : (b : Bundle0) → fore (back b) ≡ b
     sect b i = b

     retr : (u : (t : T) → Gel1 t → Gel2 t) → back (fore u) ≡ u
     retr u i t (gstrand r) = u t (gstrand r)
     retr u i t (gpoint a) = u t (gpoint a)
     retr u i t (gpath {e} r j) = u t (gpath {e = e} r j)

     thm : ((t : T) → Gel1 t → Gel2 t) ≅ Bundle0
     thm = isoToEquiv (iso fore back sect retr)

    cvtR2 : R2 → (t : T) → Gel2 t
    cvtR2 r2 t = Gel2.gstrand r2

    cvtA2 : {t : T} (e : E t) → A2 e → Gel2 t
    cvtA2 e = Interval.Endpoints.main.endpointFunc D S {A = A2} R2 f2 e

    ≅A2 : {t : T} (e : E t) → isEquiv (cvtA2 e)
    ≅A2 e = Interval.Endpoints.main.Gel-endpoints D S {A = A2} R2 f2 e

    invA2 : {t : T} (e : E t) → Gel2 t → A2 e
    invA2 e = invIsEq (≅A2 e)

    -- XXX this should be defined, not a postulate
    postulate
      ≅R2 : isEquiv cvtR2

    Rfore : (R1 → R2) → (R1 → (t : T) → Gel2 t)
    Rfore k r1 = cvtR2 (k r1)

    Rback : (R1 → (t : T) → Gel2 t) → R1 → R2
    Rback k r1 = invIsEq ≅R2 (k r1)

    Rsect : (z : (R1 → (t : T) → Gel2 t)) → Rfore (Rback z) ≡ z
    Rsect z i r1 = secIsEq ≅R2 (z r1) i

    Rretr : (z : (R1 → R2)) → Rback (Rfore z) ≡ z
    Rretr z i r1 = retIsEq ≅R2 (z r1) i

    Riso : (R1 → R2) ≅ (R1 → (t : T) → Gel2 t)
    Riso = isoToEquiv (iso Rfore Rback Rsect Rretr)

    Bundle1 : Set ℓ
    Bundle1 = Threep
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → Gel2 t)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → bm t e (f1 r1 e) ≡ (Rfore cm) r1 t)
    -- The next main step is replacing (t : T) → Gel2 t with R2
    thm01 : Bundle0 ≅ Bundle1
    thm01 = congA
       (R1 → (t : T) → Gel2 t)
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → Gel2 t)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → bm t e (f1 r1 e) ≡ cm r1 t)
       Riso

    Afore : (((t : T) (e : E t) (a1 : A1 e) → A2 e))
         → (((t : T) (e : E t) (a1 : A1 e) → Gel2 t))
    Afore k t e a1 = cvtA2 e (k t e a1)

    Aback : (((t : T) (e : E t) (a1 : A1 e) → Gel2 t))
         → (((t : T) (e : E t) (a1 : A1 e) → A2 e))
    Aback k t e a1 = invA2 e (k t e a1)

    Asect : (z : (((t : T) (e : E t) (a1 : A1 e) → Gel2 t))) → Afore (Aback z) ≡ z
    Asect z i t e a1 = secIsEq (≅A2 e) (z t e a1) i

    Aretr : (z : (((t : T) (e : E t) (a1 : A1 e) → A2 e))) → Aback (Afore z) ≡ z
    Aretr z i t e a1 = retIsEq (≅A2 e) (z t e a1) i

    Aiso : (((t : T) (e : E t) (a1 : A1 e) → A2 e))
         ≅ (((t : T) (e : E t) (a1 : A1 e) → Gel2 t))
    Aiso = isoToEquiv (iso Afore Aback Asect Aretr)

    Bundle2 : Set ℓ
    Bundle2 = Threep
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → A2 e)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → cvtA2 e (bm t e (f1 r1 e)) ≡ Gel2.gstrand (cm r1))
--     (λ cm bm → (t : T) (e : E t) (r1 : R1) → Gel2.gpoint (bm t e (f1 r1 e)) ≡ Gel2.gstrand (cm r1)) -- ← def'n-equivalently

    -- The next main step is replacing Gel2 t in the presence of e : E t with A2 e.
    thm12 : Bundle1 ≅ Bundle2
    thm12 = congB
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → Gel2 t)
       ((t : T) (e : E t) (a1 : A1 e) → A2 e)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → bm t e (f1 r1 e) ≡ (Rfore cm) r1 t)
       Aiso

    -- At this point we've got ((t : T) → Gel1 t → Gel2 t) isomorphic
    -- to something that looks a lot like a relation homomorphism.
    -- The only problem is the compatibility relation involves gel.
    -- We should be able to apply some congruences and (co)units to get
    -- rid of that.

    Bundle3 : Set ℓ
    Bundle3 = Threep
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → A2 e)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → invA2 e (Gel2.gpoint (bm t e (f1 r1 e))) ≡ invA2 e (Gel2.gstrand (cm r1)))

    thm23 : Bundle2 ≅ Bundle3
    thm23 = {!!}


    -- This is the real thing I want to obtain:
    Bundle100 : Set ℓ
    Bundle100 = Threep
       (R1 → R2)
       ((t : T) (e : E t) (a1 : A1 e) → A2 e)
       (λ cm bm → (t : T) (e : E t) (r1 : R1) → bm t e (f1 r1 e) ≡ f2 (cm r1) e)


    -- This lemma depends crucially on the normalization behavior of cvtA2
    subgoal' : (t : T) (e : E t) (r2 : R2) (a2 : A2 e) →  Gel2.gstrand r2 ≡ cvtA2 e (f2 r2 e)
    subgoal' t e r2 a2 i = Gel2.gpath {e = e} r2 (~ i)

    subgoal'' : (t : T) (e : E t) (r2 : R2) (a2 : A2 e) →  invA2 e (Gel2.gstrand r2) ≡ invA2 e (cvtA2 e (f2 r2 e))
    subgoal'' t e r2 a2 i = invA2 e (Gel2.gpath {e = e} r2 (~ i))

    subgoal : (t : T) (e : E t) (r2 : R2) (a2 : A2 e) →  invA2 e (Gel2.gstrand r2) ≡ f2 r2 e
    subgoal t e r2 a2  = cong (invIsEq (≅A2 e)) (subgoal' t e r2 a2) ∙ retIsEq (≅A2 e) (f2 r2 e)
