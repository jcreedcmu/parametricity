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
 - I'm still trying to find a good approach to Functoriality that doesn't
 - entangle everything together simultaneously. The idea here is
 - to suppose that there is some type Gel t that *happens* to be
 - isomorphic to the pushout of
 - gstrand : ((t' : T) → Gel t') → Gel t
 - gpoint : (e : E t)  → Gel t
 -}
module Interval.FunctorialityAngle where

postulate
 T : Set
 E Gel : T → Set

data View  (t : T) : Set where
 vstrand : (g : (t' : T) → Gel t') → View t
 vpoint : (e : E t) → Gel t → View t
 vpath : (e : E t) (g : (t' : T) → Gel t') → vpoint e (g t) ≡ vstrand {t} g

data ViewRec  (t : T) : Set where
 vrstrand : (g : (t' : T) → ViewRec t') → ViewRec t
 vrpoint : (e : E t) → ViewRec t → ViewRec t
 vrpath : (e : E t) (g : (t' : T) → ViewRec t') → vrpoint e (g t) ≡ vrstrand {t} g

postulate
 eq : (t : T) → Gel t ≅ View t

show : (t : T) → View t ≅ ViewRec t
show t = isoToEquiv (iso (fore t) back {!!} {!!}) where
 fore : (t : T) → View t → ViewRec t
 fore t (vstrand g) = vrstrand λ t' → fore t' (equivFun (eq t') (g t'))
 fore t (vpoint e x) = {!!}
 fore t (vpath e g i) = {!!}

 back : ViewRec t → View t
 back = {!!}
