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
 data Frame : Set₁
 record Cell (f : Frame) : Set₁
 fset : Frame → Set

 data Frame where
  fnil : Frame
  fcons : {f : Frame} (c1 c2 : Cell f) → Frame
 record Cell f where field
  Cr : Set
  Bd : fset f → Cr
 fset fnil = Void
 fset (fcons c1 c2) = Pushout (c1 .Cell.Bd) (c2 .Cell.Bd)

module _ where
 cset : {f : Frame} → Cell f → Set
 cset = Cell.Cr

 postulate
  isPushout : {A B C D : Set} (f : A → B) (g : A → C) (in1 : B → D) (in2 : C → D) → Set
  SubFrame1 : {f : Frame} → Cell f → Frame → Set -- I think this might be a prop? codomain-y
  SubFrame2 : {f : Frame} → Cell f → Frame → Set -- I think this might be a prop? domain-y

  -- realizations

  sfmap1 : {f1 f2 : Frame} {b : Cell f1} → SubFrame1 b f2 → cset b → fset f2
  sfmap2 : {f1 f2 : Frame} {b : Cell f1} → SubFrame2 b f2 → cset b → fset f2


  composable : Frame → Frame → Frame → Set

  -- should be thought of as a consequence of the cell destructor
  include : {f : Frame} (b : Cell f) → fset f → cset b

 module _ {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) where
  postulate
   common-f : Frame
   common : Cell common-f
   cinc1 : SubFrame1 common f1
   cinc2 : SubFrame2 common f2
   compose : Cell f3
   comp-inl : cset b1 → cset compose
   comp-inr : cset b2 → cset compose
   comp-set : isPushout (include b1 ∘ sfmap1 cinc1) (include b2 ∘ sfmap2 cinc2) comp-inl comp-inr

 postulate
  vcomp : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f)
      → composable (fcons A B) (fcons B C) (fcons A C)
  hzcomp : (f1 f2 f3 : Frame) (k : composable f1 f2 f3)
      (m1 : Cell f1) (n1 : Cell f1) (m2 : Cell f2) (n2 : Cell f2)
      → composable (fcons m1 n1) (fcons m2 n2) (fcons (compose m1 m2 k) (compose n1 n2 k))

  vcomp-common : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f) (cf : Cell (fcons A B)) (cg : Cell (fcons B C))
    → common-f cf cg (vcomp A B C) ≡ f
