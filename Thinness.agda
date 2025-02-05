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
open import Function.Base

module Thinness where

data two : Set where
 t0 t1 : two

record Skel : Set₁ where constructor mkSkel ; field
 A : Set
 boundary : two → A

postulate
 Path : Skel → Set
 isSpan : {s : Skel} (p : Path s) → Set -- should be a prop?
 merge : Skel → Skel → Set

record GoodSkel : Set₁ where constructor mkGoodSkel ; field
 s : Skel
 p : Path s
 j : isSpan p

postulate
 Cell1 : GoodSkel

module _ (gs1 gs2 : GoodSkel) where

 Bsh : Set
 Bsh = merge (gs1 .GoodSkel.s) (gs2 .GoodSkel.s)

 record Skel2 : Set₁ where constructor mkSkel2 ; field
  A : Set
  boundary : Bsh → A

 postulate
  Path2 : Skel2 → Set
  isSpan2 : {s : Skel2} (p : Path2 s) → Set -- should be a prop?
  merge2 : Skel2 → Skel2 → Set

 record GoodSkel2 : Set₁ where constructor mkGoodSkel2 ; field
  s : Skel2
  p : Path2 s
  j : isSpan2 p

 postulate
  Cell2 : GoodSkel2
