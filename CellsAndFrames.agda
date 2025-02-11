{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Functions.Embedding
open import Cubical.HITs.Pushout
open import Function.Base

module CellsAndFrames where

data Void : Set where

abort : (A : Set) → Void → A
abort A ()

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

module _ where
 postulate
  Frame : Set
  Cell : Frame → Set


  cset : {f : Frame} → Cell f → Set
  fset : Frame → Set

  -- prevFrame : Frame → Frame → Set -- prevFrame f1 f2 ≡ f2 is the next-lower-dimension frame contained in f1
  -- dom : Frame → Cell → Set -- dom f d ≡ d is f's domain
  -- cod : Frame → Cell → Set -- dom f c ≡ c is f's codomain

  -- a way of constructing frames
  mkFrame : {f : Frame} (c1 c2 : Cell f) → Frame

  composable : Frame → Frame → Frame → Set

  compose : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2: : Cell f2) (k : composable f1 f2 f3)
           → Cell f3

  vcomp : {f : Frame}
          (b1 : Cell f) (b2 : Cell f) (b3 : Cell f)
          → composable (mkFrame b1 b2) (mkFrame b2 b3) (mkFrame b1 b3)

  hzcomp : (f1 f2 f3 : Frame)
          (k : composable f1 f2 f3)
          (m1 : Cell f1) (n1 : Cell f1)
          (m2 : Cell f2) (n2 : Cell f2)
          → composable (mkFrame m1 n1) (mkFrame m2 n2) (mkFrame (compose m1 m2 k) (compose n1 n2 k))
