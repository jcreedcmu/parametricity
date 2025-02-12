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

-- A pushout with a definitional term that's "right in the middle"
-- of the two injections for convenience
data SymPush {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (f : A → B) (g : A → C) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  sinl : B → SymPush f g
  sinr : C → SymPush f g
  smid : A → SymPush f g
  spushl : (a : A) → smid a ≡ sinl (f a)
  spushr : (a : A) → smid a ≡ sinr (g a)


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
 fset (fcons c1 c2) = SymPush (c1 .Cell.Bd) (c2 .Cell.Bd)
open Basic

data subFrames : Frame → Set₁ where
 sfSkip : (f : Frame) (c1 c2 : Cell f) (sf : subFrames f) → subFrames (fcons c1 c2)
 sfHere : (f : Frame) → subFrames f

getSubFrame : {f : Frame} → subFrames f → Frame
getSubFrame (sfSkip f c1 c2 sf) = getSubFrame sf
getSubFrame (sfHere f) = f

-- composability

module Composability where
 open Cell
 data composable : Frame → Frame → Set₁ where
   vcomp : {f : Frame} (A : Cell f) (B : Cell f) (C : Cell f)
       → composable (fcons A B) (fcons B C)
   hzcomp : (f1 f2 : Frame) (k : composable f1 f2)
       (m1 : Cell f1) (n1 : Cell f1) (m2 : Cell f2) (n2 : Cell f2)
       → composable (fcons m1 n1) (fcons m2 n2)

-- extracting which element is in common between the two cells
-- being composed

module CommonElements where
 open Cell
 open Composability

 commonFrame : {f1 f2 : Frame} (k : composable f1 f2) → Frame
 commonFrame (vcomp {f} A B C) = f
 commonFrame (hzcomp f1 f2 k m1 n1 m2 n2) = commonFrame k

 commonCell : {f1 f2 : Frame} (k : composable f1 f2) → Cell (commonFrame k)
 commonCell (vcomp A B C) = B
 commonCell (hzcomp f1 f2 k m1 n1 m2 n2) = commonCell k

 commonSet : {f1 f2 : Frame} (k : composable f1 f2) → Set
 commonSet k = commonCell k .Cr

-- composition

module Composition where
 open Cell
 open Composability
 open CommonElements

 outputFrame : {f1 f2 : Frame} → composable f1 f2 → Frame
 composeSet : {f1 f2 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2) → Set
 composeBd : {f1 f2 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2) → fset (outputFrame k) → composeSet b1 b2 k
 compose : {f1 f2 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2) → Cell (outputFrame k)
 leftMap : {f1 f2 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2) → commonSet k → Cr b1
 rightMap : {f1 f2 : Frame} (b1 : Cell f1) (b2 : Cell f2) (k : composable f1 f2) → commonSet k → Cr b2
 leftFmap : {f1 f2 : Frame} (k : composable f1 f2) → commonSet k → fset f1
 rightFmap : {f1 f2 : Frame} (k : composable f1 f2) → commonSet k → fset f2

 outputFrame (vcomp A B C) = fcons A C
 outputFrame (hzcomp f1 f2 k m1 n1 m2 n2) = fcons (compose m1 m2 k) (compose n1 n2 k)

 composeSet b1 b2 k = SymPush (leftMap b1 b2 k) (rightMap b1 b2 k)

 leftMap b1 b2 k csx = b1 .Bd (leftFmap k csx)
 rightMap b1 b2 k csx = b2 .Bd (rightFmap k csx)

 leftFmap (vcomp A B C) csx = sinr csx
 leftFmap (hzcomp f1 f2 k m1 n1 m2 n2) csx = smid (leftFmap k csx)
 rightFmap (vcomp A B C) csx = sinl csx
 rightFmap (hzcomp f1 f2 k m1 n1 m2 n2) csx = smid (rightFmap k csx)

 composeBd cf cg (vcomp A B C) (sinl x) = inl1 (cf .Bd (inl2 x)) where
  inl1 : Cr cf → SymPush (λ csx → cf .Bd (sinr csx)) (λ csx → cg .Bd (sinl csx))
  inl1 = sinl

  inl2 : Cr A → SymPush (A .Bd) (B .Bd)
  inl2 = sinl
 composeBd cf cg (vcomp A B C) (sinr x) = inr1 (cg .Bd (inr2 x)) where
  inr1 : Cr cg → SymPush (λ csx → cf .Bd (sinr csx)) (λ csx → cg .Bd (sinl csx))
  inr1 = sinr

  inr2 : Cr C → SymPush (B .Bd) (C .Bd)
  inr2 = sinr

 composeBd cf cg (k@(vcomp A B C)) (smid x) = rv where
  -- rv : composeSet cf cg (vcomp A B C)
  rv : SymPush (λ csx → cf .Bd (sinr csx)) (λ csx → cg .Bd (sinl csx))
  rv = smid (Bd B x)

-- For the path case we need
-- inl1 (cf .Bd (inl2 (A .Bd a))) ≡ inr1 (cg .Bd (inr2 (C .Bd a)))

-- need:
-- i = i0 ⊢ smid (B .Bd a)
-- i = i1 ⊢ sinl (cf .Bd (sinl (A .Bd a)))
 composeBd cf cg (k@(vcomp A B C)) (spushl a i) = (spushl (Bd B a) ∙ lemma) i where
  lemma : sinl (leftMap cf cg (vcomp A B C) (Bd B a)) ≡ sinl (cf .Bd (sinl (A .Bd a)))
  lemma i = sinl (Bd cf ((sym (spushr a) ∙ spushl a) i))
-- need:
-- i = i0 ⊢ smid (B .Bd a)
-- i = i1 ⊢ sinr (b2 .Bd (sinr (C .Bd a)))
 composeBd cf cg (k@(vcomp A B C)) (spushr a i) = (spushr (Bd B a) ∙ lemma) i where
  lemma : sinr (rightMap cf cg (vcomp A B C) (Bd B a)) ≡ sinr (cg .Bd (sinr (C .Bd a)))
  lemma i = sinr (Bd cg ((sym (spushl a) ∙ spushr a) i))

  --   (cong (λ q → cinl (cf .Bd q)) (push a)
  --    ∙ push (B .Bd a)
  --    ∙ cong (λ q → cinr (cg .Bd q)) (push a)) i where
  -- -- This type information is necessary
  -- cinl : cf .Cr → composeSet cf cg k
  -- cinl = inl
  -- cinr : cg .Cr → composeSet cf cg k
  -- cinr = inr

 composeBd α β (hzcomp f1 f2 k m1 n1 m2 n2) (sinl x) = {!!}
 composeBd α β (hzcomp f1 f2 k m1 n1 m2 n2) (sinr x) = {!!}
 composeBd α β (hzcomp f1 f2 k m1 n1 m2 n2) (smid x) = {!!}
 composeBd α β (hzcomp f1 f2 k m1 n1 m2 n2) (spushl a i) = {!!}
 composeBd α β (hzcomp f1 f2 k m1 n1 m2 n2) (spushr a i) = {!!}

 compose α β k = mkCell (composeSet α β k) (composeBd α β k)
