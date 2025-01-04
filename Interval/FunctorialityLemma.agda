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
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base
import Interval.Gel

{-
 - Here I'm trying to show, independent of any interval axioms, that
 - the Gel pushout satisfies an equivalence between
 - (t : T) → Gel t → H t
 - and a record of
 - c : ((t : T) → Gel t) → ((t : T) → H t) (the "coarse" function between global elements)
 - eu : {t : T} (e : E t) → Gel t → H t (the "endpoint-uniform" function)
 - {t : T} (e : E t) (g : (t : T) → Gel t) → eu e (g t) ≡ c g t
 -}
module Interval.FunctorialityLemma where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

  module _ {A : {t : T} (e : E t) → Set ℓ}
           (R : Set ℓ) (H : T → Set ℓ)
           (f : (r : R) {t : T} (e : E t) → A e)
   where
   module toOpen = Interval.Gel.main.gel {ℓ1} {ℓ2} D S R f
   open toOpen using (Gel ; gstrand ; gpoint ; gpath)

   record Pack : Set ℓ where
    constructor pack
    field
     coarse : ((t : T) → Gel t) → ((t : T) → H t)
     fine : {t : T} (e : E t) → Gel t → H t
     compat : {t : T} (e : E t) (g : (t : T) → Gel t) → fine e (g t) ≡ coarse g t

   fore : ((t : T) → Gel t → H t) → Pack
   fore u = pack coarse fine compat where
     coarse : ((t : T) → Gel t) → ((t : T) → H t)
     coarse g t = u t (g t)
     fine : {t : T} (e : E t) → Gel t → H t
     fine {t} e g = u t g
     compat : {t : T} (e : E t) (g : (t : T) → Gel t) → fine e (g t) ≡ coarse g t
     compat {t} e g i = u t (g t)

   back : Pack → ((t : T) → Gel t → H t)
   back p t (gstrand r) = p .Pack.coarse  (λ t → gstrand r) t
   back p t g@(gpoint {e} a) = p .Pack.fine e g
   back p t (gpath {e} r i) = (cong (p .Pack.fine e) (gpath {e = e} r) ∙ p .Pack.compat e (λ t → gstrand r)) i

   sect : (p : Pack) → fore (back p) ≡ p
   sect = {!!}

   foo : (u : (t : T) → Gel t → H t) (t : T) (e : E t) (r : R) (j : I)
         →  ((λ k → u t (gpath {e = e} r k)) ∙ refl) j -- this refl is actually (λ k → u t (gstrand r))
        ≡  u t (gpath {e = e} r j)
-- cong f p  = λ i → f (p i)

   foo u t e r j =  cong (λ q → q j) (sym (rUnit (λ k → u t (gpath {e = e} r k))))

   retr : (u : (t : T) → Gel t → H t) → back (fore u) ≡ u
   retr u i t (gstrand r) = u t (gstrand r)
   retr u i t (gpoint a) = u t (gpoint a)
   retr u i t (gpath {e} r j) = foo u t e r j i
