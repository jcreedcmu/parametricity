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

module Interval.FunctorialityWarmup where

data X : Set where
 t0 t1 : X

postulate
  T : Set
  η : X → T

module mGel (A : X → Set) (R : ((x : X) → A x) → Set) where

  AA = ((x : X) → A x)

  data Gel : T → Set where
    gstrand : {t : T} {aa : AA} (r : R aa) → Gel t
    gpoint : {x : X} (a : A x) → Gel (η x)
    gpath : {x : X} (aa : AA) (r : R aa) → gpoint (aa x) ≡ gstrand r

  geq : Σ AA R → (t : T) → Gel t
  geq (aa , r) t = gstrand r

  eeq : (x : X) (a : A x) → Gel (η x)
  eeq x a = gpoint a

  postulate
    geqIsEq : isEquiv geq
    eeqIsEq : (x : X) → isEquiv (eeq x)

module twGel (A1 : X → Set) (R1 : ((x : X) → A1 x) → Set)
             (A2 : X → Set) (R2 : ((x : X) → A2 x) → Set)
             (ah : (x : X) → A1 x → A2 x)
             where
 module m1 = mGel A1 R1
 module m2 = mGel A2 R2

 data GoodFuncOver : ((x : X) → A1 x → A2 x) → Set where
   gfo : (f : (t : T) → m1.Gel t → m2.Gel t) → GoodFuncOver λ x a1 → invIsEq (m2.eeqIsEq x) (f (η x) (m1.eeq x a1))

 data MidFuncOver : ((x : X) → A1 x → A2 x) → Set where
   mfo : (ah : ((x : X) → A1 x → A2 x))
         (f : ((t : T) → m1.Gel t) → ((t : T) → m2.Gel t))
         (compat : (g : (t : T) → m1.Gel t) (x : X) → f g (η x) ≡ {! g (η x)!})
         → MidFuncOver ah
