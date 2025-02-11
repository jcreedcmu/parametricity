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

postulate
 isPushout : {A B C D : Set} (f : A → B) (g : A → C) (in1 : B → D) (in2 : C → D) → Set

module _ where
 postulate
  Frame : Set
  Cell : Frame → Set

  -- realizations
  cset : {f : Frame} → Cell f → Set
  fset : Frame → Set

  -- how to construct frames
  fnil : Frame
  fcons : {f : Frame} (c1 c2 : Cell f) → Frame

  -- how to construct cells
  mkcell : (f : Frame) (Cr : Set) → (fset f → Cr) → Cell f

  composable : Frame → Frame → Frame → Set

 module _ {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) where
  postulate
   common : Set
   cinc1 : common → cset b1
   cinc2 : common → cset b2
   compose : Cell f3
   comp-inl : cset b1 → cset compose
   comp-inr : cset b2 → cset compose
   comp-set : isPushout cinc1 cinc2 comp-inl comp-inr

 postulate
  -- should be thought of as a consequence of the cell destructor
  include : {f : Frame} (b : Cell f) → fset f → cset b

  fnil-set : fset fnil ≡ Void
  fcons-inl : {f : Frame} {c1 c2 : Cell f} → cset c1 → fset (fcons c1 c2)
  fcons-inr : {f : Frame} {c1 c2 : Cell f} → cset c2 → fset (fcons c1 c2)
  fcons-set : {f : Frame} {c1 c2 : Cell f}
       → isPushout (include c1) (include c2) fcons-inl fcons-inr

  vcomp : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f)
      → composable (fcons A B) (fcons B C) (fcons A C)
  hzcomp : (f1 f2 f3 : Frame) (k : composable f1 f2 f3)
      (m1 : Cell f1) (n1 : Cell f1) (m2 : Cell f2) (n2 : Cell f2)
      → composable (fcons m1 n1) (fcons m2 n2) (fcons (compose m1 m2 k) (compose n1 n2 k))

  vcomp-common : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f) (cf : Cell (fcons A B)) (cg : Cell (fcons B C))
    → common cf cg (vcomp A B C) ≡ cset B
