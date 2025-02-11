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


module Basic where
 data Frame : Set₁
 record Cell (f : Frame) : Set₁
 fset : Frame → Set

 data Frame where
  fnil : Frame
  fcons : {f : Frame} (c1 c2 : Cell f) → Frame
 record Cell f where constructor mkCell ; field
  Cr : Set
  Bd : fset f → Cr
 fset fnil = Void
 fset (fcons c1 c2) = Pushout (c1 .Cell.Bd) (c2 .Cell.Bd)
open Basic

data subFrames : Frame → Set₁ where
 sfSkip : (f : Frame) (c1 c2 : Cell f) (sf : subFrames f) → subFrames (fcons c1 c2)
 sfHere : (f : Frame) → subFrames f

getSubFrame : {f : Frame} → subFrames f → Frame
getSubFrame (sfSkip f c1 c2 sf) = getSubFrame sf
getSubFrame (sfHere f) = f

-- composition

module Composition where
 open Cell
 data composable : Frame → Frame → Frame → Set₁
 composeSet : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → Set
 composeBd : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → fset f3 → composeSet b1 b2 k
 compose : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → Cell f3
 commonSet : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → Set
 leftMap : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → commonSet b1 b2 k → Cr b1
 rightMap : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → commonSet b1 b2 k → Cr b2

 data composable where
   vcomp : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f)
       → composable (fcons A B) (fcons B C) (fcons A C)
   hzcomp : (f1 f2 f3 : Frame) (k : composable f1 f2 f3)
       (m1 : Cell f1) (n1 : Cell f1) (m2 : Cell f2) (n2 : Cell f2)
       → composable (fcons m1 n1) (fcons m2 n2) (fcons (compose m1 m2 k) (compose n1 n2 k))

 composeSet b1 b2 k = Pushout (leftMap b1 b2 k) (rightMap b1 b2 k)
 composeBd b1 b2 k = {!!}
 compose b1 b2 k = mkCell (composeSet b1 b2 k) (composeBd b1 b2 k)
 commonSet b1 b2 (vcomp A B C) = Cr B
 commonSet b1 b2 (hzcomp f1 f2 f3 k m1 n1 m2 n2) = {!!}
 leftMap = {!!}
 rightMap = {!!}

 --   comp-set : isPushout (include b1 ∘ sfmap1 cinc1) (include b2 ∘ sfmap2 cinc2) comp-inl comp-inr
