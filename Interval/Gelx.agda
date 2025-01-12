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
import Interval.Geli

-- Gel, with an embedding rather than a prop fiber for endpoints

module Interval.Gelx where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

  disc : ∀ {ℓ0} → Set ℓ0 → Set (ℓ ⊔ ℓ0)
  disc A = bridgeDiscrete T A

 module mainsigma {A : Σ T E → Set ℓ} (R : (aa : (s : Σ T E) → A s) → Set ℓ)  where
   Agen : {t : T} (e : E t) → Set ℓ
   Agen {t} e = A (t , e)

   Rgen : ({t : T} (e : E t) → Agen e) → Set ℓ
   Rgen aa = R (λ s → aa (s .snd))

   open Interval.Geli.maini D S Rgen hiding (thm)

   data Gels : T → Set ℓ where
        gstrands : {t : T} (aa : (s : Σ T E) → A s) (r : R aa) → Gels t
        gpoints : {s : Σ T E} (a : A s) → Gels (s .fst)
        gpaths : {s : Σ T E} (aa : (s : Σ T E) → A s) (r : R aa) → gpoints (aa s) ≡ gstrands aa r

   thm : (t : T) → Geli t ≅ Gels t
   thm t = isoToEquiv (iso fore {!!} {!!} {!!}) where
    fore : Geli t → Gels t
    fore (gstrandi aa r) = gstrands (λ s → aa (s .snd)) r
    fore (gpointi a) = gpoints a
    fore (gpathi {e} aa r i) = gpaths {s = (t , e)} (λ s → aa (s .snd)) r i

    back : Gels t → Geli t
    back (gstrands aa r) = gstrandi (λ {t} e → aa (t , e)) r
    back (gpoints {t , e} a) = gpointi {e = e} a
    back (gpaths {t , e} aa r i) = gpathi {e = e} (λ {t} e → aa (t , e)) r i



 module mainx {A : S → Set ℓ} (R : (aa : (s : S) → A s) → Set ℓ)  where

   Agen : {t : T} (e : E t) → Set ℓ
   Agen (s , p) = A s

   Rgen : ({t : T} (e : E t) → Agen e) → Set ℓ
   Rgen aa = R λ s → aa (s , refl)

   open Interval.Geli.maini D S Rgen hiding (thm)

   data Gelx (t : T) : Set ℓ where
        gstrandx : (aa : (s : S) → A s) (r : R aa) → Gelx t
        gpointx : {s : S} (a : A s) → Gelx t
        gpathx : {s : S} (aa : (s : S) → A s) (r : R aa) → gpointx (aa s) ≡ gstrandx aa r

   thm : (t : T) → Geli t ≅ Gelx t
   thm t = isoToEquiv (iso fore {!!} {!!} {!!}) where
    fore : Geli t → Gelx t
    fore (gstrandi aa r) = gstrandx {!!} {!!}
    fore (gpointi a) = {!!}
    fore (gpathi aa r i) = {!!}

   --  back : Geli t → Gel t
   --  back (gstrandi aa r) = gstrand (aa , r)
   --  back (gpointi a) = gpoint a
   --  back (gpathi {e} aa r i) = gpath {e = e} (aa , r) i

   --  sect : (g : Geli t) → fore (back g) ≡ g
   --  sect (gstrandi aa r) i = gstrandi aa r
   --  sect (gpointi a) i = gpointi a
   --  sect (gpathi {e} aa r i) j = gpathi {e = e} aa r i

   --  retr : (g : Gel t) → back (fore g) ≡ g
   --  retr (gstrand r) i = gstrand r
   --  retr (gpoint a) i = gpoint a
   --  retr (gpath{e} r i) j = gpath {e = e} r i
