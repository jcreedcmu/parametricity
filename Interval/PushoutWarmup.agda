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
 - Practicing substituting isomorphisms into pushouts.
 - Probably could do this with univalence as well,
 - although I ran into fiddly level issues last time I tried.
 -}
module Interval.PushoutWarmup (A : Set) (A' : Set) (B : Set) (C : Set) (f : C → A) (g : C → B)
  (into : A → A') (intoEq : isEquiv into)
  where

P : Set
P = Push f g

Q : Set
Q = Push (into ∘ f) g

fore : P → Q
fore (pinl a) = pinl (into a)
fore (pinr b) = pinr b
fore (ppath c i) = ppath c i

-- i = i0 ⊢ pinr (g c)
-- i = i1 ⊢ pinl (invIsEq intoEq (into (f c)))
back : Q → P
back (pinl a) = pinl (invIsEq intoEq a)
back (pinr b) = pinr b
back (ppath c i) = (ppath c ∙ λ j → pinl (retIsEq intoEq (f c) (~ j)) ) i

blah : (c : C) → {!(ppath c ∙ λ j → pinl (retIsEq intoEq (f c) (~ j)) )!}
blah = {!!}
-- pinr (g c)
-- pinl (secIsEq intoEq (f c) i)

foo = (c : C) →  {!(λ (i : I) →  pinl (secIsEq intoEq (into (f c)) i))!}
foo2 = (c : C) →  {!( pinl (secIsEq intoEq (into (f c)) i0))!}
-- hardMap : (c : C) → PathP (λ i → {!Q  !} (λ i → pinr (g c)) (λ i →  pinl (secIsEq intoEq (into (f c)) i))
-- -- pinr (g c) ≡ pinl {f = into ∘ f} {g = g} (secIsEq intoEq (into (f c)) i)
-- hardMap = {!!}

module _ (D : Q → Set)
  (af : (a' : A') → D (pinl a'))
  (bf : (b : B) → D (pinr b))
  (cf : (c : C) → PathP (λ i → D (ppath c i)) (bf (g c)) (af (into (f c))))
  where
 Qelim : (q : Q)  → D q
 Qelim (pinl a) = af a
 Qelim (pinr b) = bf b
 Qelim (ppath c i) = cf c i

hardMap : (c : C) → PathP (λ i → fore (back (ppath c i)) ≡ (ppath c i))
       (λ i → pinr (g c))
       (λ i → pinl (secIsEq intoEq (into (f c)) i))
hardMap = {!!}

sect : (q : Q) → fore (back q) ≡ q
sect (pinl a') i = pinl (secIsEq intoEq a' i)
sect (pinr b) i = pinr b
sect (ppath c i) = hardMap c i

thm : P ≅ Q
thm = isoToEquiv (iso fore back {!!} {!!})
