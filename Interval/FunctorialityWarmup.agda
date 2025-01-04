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
             where
 module m1 = mGel A1 R1
 module m2 = mGel A2 R2

 E1 : X → Set
 E1 x = m1.Gel (η x)

 E2 : X → Set
 E2 x = m2.Gel (η x)

 data GoodFunc : Set where
   gfo : (f : (t : T) → m1.Gel t → m2.Gel t) → GoodFunc

 record MidFunc : Set where
   constructor mfo
   field
     ah : ((x : X) → E1 x → E2 x)
     f : ((t : T) → m1.Gel t) → ((t : T) → m2.Gel t)
     compat : (g : (t : T) → m1.Gel t) (x : X) → ah x (g (η x)) ≡ f g (η x)

 goodToMid : GoodFunc → MidFunc
 goodToMid (gfo f) = mfo (f ∘ η) (λ g t → f t (g t)) λ g x i → f (η x) (g (η x))

 module _ where
  private

   indf : (mf : MidFunc) (t : T) → m1.Gel t → m2.Gel t
   indf mf t (m1.gstrand r) = mf .MidFunc.f (λ t → m1.gstrand r) t
   indf mf .(η _) g@(m1.gpoint {x} a) = mf .MidFunc.ah x g
   indf mf .(η _) (m1.gpath {x} aa r i) = (cong (mf .MidFunc.ah x) (m1.gpath aa r) ∙ mf .MidFunc.compat (λ t → m1.gstrand r) x) i

   back : MidFunc → GoodFunc
   back mf = gfo (indf mf)

   sect : (m : MidFunc) → goodToMid (back m) ≡ m
   sect m i = mfo (λ x e1 → {!!}) {!!} {!!}

   retr : (f : GoodFunc) → back (goodToMid f) ≡ f
   retr (gfo f) i = gfo (indfp i) where
     indfp : (indf (mfo (f ∘ η) (λ g t → f t (g t)) (λ g x _ → f (η x) (g (η x))))) ≡ f
     indfp i t g@(mGel.gstrand r) = f t g
     indfp i t g@(mGel.gpoint {x} a) = f t g
     indfp i .(η _) (mGel.gpath aa r j) = {!!}
  thm : GoodFunc ≅ MidFunc
  thm = isoToEquiv (iso goodToMid back sect retr)
