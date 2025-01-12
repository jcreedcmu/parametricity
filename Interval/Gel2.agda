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

-- Gel, specifically for binary relations

module Interval.Gel2 where

data two : Set where
 t0 t1 : two

module _ {ℓ1 : Level} (D : Set ℓ1) where
 private
  ℓ = ℓ1
  T = D ▻ two
  E = End

 module main2 {A B : Set ℓ} (R : A → B → Set ℓ)  where

   Agen : {t : T} (e : E t) → Set ℓ
   Agen (t0 , p) = A
   Agen (t1 , p) = B

   Rgen : ({t : T} (e : E t) → Agen e) → Set ℓ
   Rgen a = R (a (t0 , refl)) (a (t1 , refl))

   open Interval.Geli.maini D two Rgen hiding (thm)

   data Gel2 (t : T) : Set ℓ where
        gstrand2 : (a : A) (b : B) (r : R a b) → Gel2 t
        gpointa2 : (a : A) → Gel2 t
        gpointb2 : (b : B) → Gel2 t
        gpatha2 : (a : A) (b : B) (r : R a b) → gpointa2 a ≡ gstrand2 a b r
        gpathb2 : (a : A) (b : B) (r : R a b) → gpointb2 b ≡ gstrand2 a b r

   cvta : {t : T} {e : E t} → Agen e → Gel2 t
   cvta {e = t0 , p} a = gpointa2 a
   cvta {e = t1 , p} b = gpointb2 b

   patha : {t : T} (e : E t) (aa : {t : T} (e : E t) → Agen e)
            (r : R (aa (t0 , refl)) (aa (t1 , refl)))
          → cvta (aa e) ≡ gstrand2 (aa (t0 , refl)) (aa (t1 , refl)) r
   patha (t0 , p) aa r = {!gpatha2 (aa (t0 , refl)) (aa (t1 , refl)) r !}
   patha (t1 , p) aa r = {!!}


   thm : (t : T) → Geli t ≅ Gel2 t
   thm t = isoToEquiv (iso fore {!!} {!!} {!!}) where
    fore : Geli t → Gel2 t
    fore (gstrandi aa r) = gstrand2 (aa (t0 , refl)) (aa (t1 , refl)) r
    fore (gpointi a) = cvta a
    fore (gpathi {e} aa r i) = patha e aa r i

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
