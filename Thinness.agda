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

record Skel : Set₁ where constructor mkSkel ; field
 A : Set
 a a' : A

postulate
 Path : Skel → Set
 isSpan : {s : Skel} (p : Path s) → Set -- should be a prop?
 merge : Skel → Skel → Set

 Arrow : Set
 a0 a1 : Arrow

record GoodSkel : Set₁ where constructor mkGoodSkel ; field
 s : Skel
 p : Path s
 j : isSpan p

arrowSkel : Skel
arrowSkel = mkSkel Arrow a0 a1

postulate
 arrowPath : Path arrowSkel
 arrowPathIsSpan : isSpan arrowPath

 Cell2 : (gs1 gs2 : GoodSkel) → Set
 Cell2Boundary : (gs1 gs2 : GoodSkel) → merge (gs1 .GoodSkel.s) (gs2 .GoodSkel.s) → Cell2 gs1 gs2
