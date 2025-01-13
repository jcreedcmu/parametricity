{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
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
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module Interval.Sketch where

data Tree : Set where
 leaf : Tree
 arrow : Tree → Tree → Tree

module _ (A : Set) where
 interp : Tree → Set
 interp leaf = A
 interp (arrow t u) = (interp t) → (interp u)

postulate
  ♯2 : Set
  p0 p1 : ♯2

module _ {ℓ : Agda.Primitive.Level} (A : ♯2 → Set ℓ) where
  postulate
    Bridge : A p0 → A p1 → Set ℓ

module _ {ℓ : Agda.Primitive.Level} {A : ♯2 → Set ℓ} where
  postulate
    pabs : (f : (i : ♯2) → A i) → Bridge A (f p0) (f p1)
    papp : {a0 : A p0} {a1 : A p1} → Bridge A a0 a1 → (i : ♯2) → A i
    pβ : (f : (i : ♯2) → A i) (i : ♯2) → papp (pabs f) i ≡p f i
    {-# REWRITE pβ #-}
    pβ0 : {a0 : A p0} {a1 : A p1} (p : Bridge A a0 a1) → papp p p0 ≡p a0
    {-# REWRITE pβ0 #-}
    pβ1 : {a0 : A p0} {a1 : A p1} (p : Bridge A a0 a1) → papp p p1 ≡p a1
    {-# REWRITE pβ1 #-}
    pη : {a0 : A p0} {a1 : A p1} (p : Bridge A a0 a1) → pabs (λ i → papp p i) ≡p p
    {-# REWRITE pη #-}


module _ (A B : Set) (R : A → B → Set) where

 postulate
  Gel : ♯2 → Set
  Gel0 : Gel p0 ≡p A
  {-# REWRITE Gel0 #-}
  Gel1 : Gel p1 ≡p B
  {-# REWRITE Gel1 #-}

  gel : {a : A} {b : B} → R a b → Bridge Gel a b
  ungel : {a : A} {b : B} → Bridge Gel a b → R a b

 inrel : (u : Tree) → interp A u → interp B u → Set
 inrel leaf a b = R a b
 inrel (arrow u1 u2) f g = {a : interp A u1} {b : interp B u1}
                   → inrel u1 a b → inrel u2 (f a) (g b)


 lemma : (u : Tree) {a : interp A u} {b : interp B u} → Bridge (λ z → interp (Gel z) u) a b → inrel u a b
 lemma-inv : (u : Tree) {a : interp A u} {b : interp B u} (g : inrel u a b) → Bridge (λ z → interp (Gel z) u) a b


 lemma leaf p = ungel p
 lemma (arrow u1 u2) {a} {b} func {aa} {bb} rr = lemma u2 (pabs λ z → (papp func z) (papp arg z)) where
  arg : Bridge (λ z → interp (Gel z) u1) aa bb
  arg = lemma-inv u1 rr

 hoist : {u1 u2 : Tree} {af : interp A u1 → interp A u2} {bf : interp B u1 → interp B u2}
         → ({a : interp A u1} {b : interp B u1} (r : Bridge (λ z → interp (Gel z) u1) a b)
                → Bridge (λ z → interp (Gel z) u2) (af a) (bf b))
         → Bridge (λ z → interp (Gel z) u1 → interp (Gel z) u2) af bf
 hoist = {!!}

 lemma-inv leaf rr = gel rr
 lemma-inv (arrow u1 u2) {af} {bf} rr = hoist (λ r → lemma-inv u2 (rr (lemma u1 r)))

 parametricity : (u : Tree) (pf : (A : Set) → interp A u)
                 → inrel u (pf A) (pf B)
 parametricity u pf = lemma u (pabs λ (t : ♯2) → pf (Gel t))
