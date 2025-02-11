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
 commonFrame : {f1 f2 f3 : Frame} (k : composable f1 f2 f3) → Frame
 commonCell : {f1 f2 f3 : Frame} (k : composable f1 f2 f3) → Cell (commonFrame k)
 commonSet : {f1 f2 f3 : Frame} (k : composable f1 f2 f3) → Set
 leftMap : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → commonSet k → Cr b1
 rightMap : {f1 f2 f3 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2 f3) → commonSet k → Cr b2

 data composable where
   vcomp : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f)
       → composable (fcons A B) (fcons B C) (fcons A C)
   hzcomp : (f1 f2 f3 : Frame) (k : composable f1 f2 f3)
       (m1 : Cell f1) (n1 : Cell f1) (m2 : Cell f2) (n2 : Cell f2)
       → composable (fcons m1 n1) (fcons m2 n2) (fcons (compose m1 m2 k) (compose n1 n2 k))

 commonFrame (vcomp {f} A B C) = f
 commonFrame (hzcomp f1 f2 f3 k m1 n1 m2 n2) = commonFrame k
 commonCell (vcomp A B C) = B
 commonCell (hzcomp f1 f2 f3 k m1 n1 m2 n2) = commonCell k
 commonSet k = commonCell k .Cr
 composeSet b1 b2 k = Pushout (leftMap b1 b2 k) (rightMap b1 b2 k)
 leftMap b1 b2 (vcomp A B C) csx = b1 .Bd (inr csx)
 leftMap b1 b2 (hzcomp f1 f2 f3 k m1 n1 m2 n2) csx = {!!}
 rightMap b1 b2 (vcomp A B C) csx = b2 .Bd (inl csx)
 rightMap b1 b2 (hzcomp f1 f2 f3 k m1 n1 m2 n2) csx = {!!}

 composeBd b1 b2 (vcomp A B C) (inl x) = inl1 (b1 .Bd (inl2 x)) where
  inl1 : Cr b1 → Pushout (λ csx → b1 .Bd (inr csx)) (λ csx → b2 .Bd (inl csx))
  inl1 = inl

  inl2 : Cr A → Pushout (A .Bd) (B .Bd)
  inl2 = inl
 composeBd b1 b2 (vcomp A B C) (inr x) = inr1 (b2 .Bd (inr2 x)) where
  inr1 : Cr b2 → Pushout (λ csx → b1 .Bd (inr csx)) (λ csx → b2 .Bd (inl csx))
  inr1 = inr

  inr2 : Cr C → Pushout (B .Bd) (C .Bd)
  inr2 = inr

-- For the path case we need
-- inl1 (b1 .Bd (inl2 (A .Bd a))) ≡ inr1 (b2 .Bd (inr2 (C .Bd a)))
 composeBd b1 b2 (k@(vcomp A B C)) (push a i) =
    (cong (λ q → cinl (b1 .Bd q)) (push a)
     ∙ push (B .Bd a)
     ∙ cong (λ q → cinr (b2 .Bd q)) (push a)) i where
  -- This type information is necessary
  cinl : b1 .Cr → composeSet b1 b2 k
  cinl = inl
  cinr : b2 .Cr → composeSet b1 b2 k
  cinr = inr

 composeBd b1 b2 (hzcomp f1 f2 f3 k m1 n1 m2 n2) = {!!}
 compose b1 b2 k = mkCell (composeSet b1 b2 k) (composeBd b1 b2 k)
