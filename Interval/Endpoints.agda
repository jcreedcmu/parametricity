{-# OPTIONS --cubical --rewriting --allow-unsolved-metas #-}

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
import Interval.PropSigmaReduce

{-
 - The point of this is to show that when t is an endpoint (i.e. E t holds)
 - then the type Gel t is isomorphic to the prescribed endpoint set.
 -}

module Interval.Endpoints where

-- A slightly abstracted form of retr-lemma below
private
 lemma-abs : ∀ {ℓ} (E B : Set ℓ) (p : E → B) (e e' : E) (q : e' ≡ e) (b : B) (h : (e : E) → p e ≡ b) →
         Square (λ j → p (q j)) (λ j → h e' j)
                (λ i → p e') (λ i → h e i)
 lemma-abs E B p e e' q b h i j = hcomp (λ k → λ {
    (i = i0) → p (q j) ;
    (j = i0) → h e' (i ∧ ~ k) ;
    (i = i1) → h e' (j ∨ ~ k) ;
    (j = i1) → h e i
  }) (h (q j) i)

module main {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

 module _ {A : {t : T} (e : E t) → Set ℓ} (R : Set ℓ) (f : (r : R) {t : T} (e : E t) → A e) where
  open Interval.Gel.main.gel {ℓ1} {ℓ2} D S R f

  private
   fore : {t : T} (e : E t) → Gel t → (Σ[ e ∈ E t ] A e)
   fore e (gstrand r) = e , (f r e)
   fore e (gpoint {e = e'} a) = e' , a
   fore {t} e (gpath {e = e'} r i) = EndIsProp t e' e i , f r (EndIsProp t e' e i)

   back : {t : T} → Σ (E t) A → Gel t
   back (e , a) = gpoint a

   sect : {t : T} (e : E t) → (g : Σ (E t) A) → fore e (back g) ≡ g
   sect e s i = s

   retr-lemma : (r : R) (t : T) (e e' : E t) →
           Square (λ j → gpoint (f r (EndIsProp t e' e j))) (λ j → gpath {e = e'} r j)
                  (λ i → gpoint (f r e')) (λ i → gpath {e = e} r i)
   retr-lemma r t e e' = lemma-abs (E t) (Gel t) (λ e → gpoint (f r e)) e e' (EndIsProp t e' e) (gstrand r) (λ e → gpath {e = e} r)

   retr : {t : T} (e : E t) (g : Gel t) → back (fore e g) ≡ g
   retr e (gstrand r) i = (gpath {e = e} r i)
   retr {t} e (gpoint {e = e'} a) i = gpoint a
   retr {t} e (gpath {e = e'} r j) i = retr-lemma r t e e' i j

  sumeq : {t : T} (e : E t) → Σ (E t) A ≅ Gel t
  sumeq e =  isoToEquiv (Cubical.Foundations.Isomorphism.iso back (fore e) (retr e) (sect e))

  endpointFunc : {t : T} (e : E t) → A e → Gel t
  endpointFunc e a = gpoint a

  Gel-endpoints : {t : T} (e : E t) → isEquiv (endpointFunc e)
  Gel-endpoints {t} e = Interval.PropSigmaReduce.thm  (E t) A (Gel t) (EndIsProp t) endpointFunc (sumeq e .snd) e
