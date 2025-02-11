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
  Cell : Set
  Frame : Set

  frameOf : Cell → Frame → Set -- frameOf c f ≡ c's frame is f

  cset : Cell → Set
  fset : Frame → Set

  prevFrame : Frame → Frame → Set -- prevFrame f1 f2 ≡ f2 is the next-lower-dimension frame contained in f1
  dom : Frame → Cell → Set -- dom f d ≡ d is f's domain
  cod : Frame → Cell → Set -- dom f c ≡ c is f's codomain

  -- a way of constructing frames
  mkFrame : {f : Frame} {c1 c2 : Cell} → frameOf c1 f → frameOf c2 f → Frame

  composable : Frame → Frame → Frame → Set

 module _ {f1 f2 f3 : Frame} {b1 b2 : Cell}
          (of1 : frameOf b1 f1) (of2 : frameOf b2 f2) (k : composable f1 f2 f3)
          where
  postulate
   compose : Cell
   composeFrame : frameOf compose f3

 postulate
  vcomp : {f : Frame} {b1 b2 b3 : Cell}
          (of1 : frameOf b1 f) (of2 : frameOf b2 f) (of3 : frameOf b3 f)
          → composable (mkFrame of1 of2) (mkFrame of2 of3) (mkFrame of1 of3)
  hzcomp : (f1 f2 f3 : Frame)
           (k : composable f1 f2 f3) (m1 m2 n1 n2 : Cell)
           (ofm1 : frameOf m1 f1) (ofn1 : frameOf n1 f1)
           (ofm2 : frameOf m2 f2) (ofn2 : frameOf n2 f2)
           → composable (mkFrame ofm1 ofn1) (mkFrame ofm2 ofn2) (mkFrame (composeFrame ofm1 ofm2 k) (composeFrame ofn1 ofn2 k))
