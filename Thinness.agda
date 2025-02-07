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

module Thinness where

data Void : Set where

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

record Ball1 (S : Set) : Set₁ where field
 Cr : Set
 Bd : S → Cr

postulate
 C1 : Ball1 two

module _ (C D : Ball1 two) where
 b1comp : Ball1 two
 Ball1.Cr b1comp = Pushout (λ (x : Unit) → C .Ball1.Bd t1) (λ (x : Unit) → D .Ball1.Bd t0)
 Ball1.Bd b1comp t0 = inl (C .Ball1.Bd t0)
 Ball1.Bd b1comp t1 = inr (D .Ball1.Bd t1)

record Ball2 (S : Set) (Bd1a Bd1b : Ball1 S) : Set₁ where field
 Cr : Set
 Bd : Pushout (Bd1a .Ball1.Bd) (Bd1b .Ball1.Bd) → Cr

record Ball3 (S : Set) (Bd1a Bd1b : Ball1 S) (Bd2a Bd2b : Ball2 S Bd1a Bd1b) : Set₁ where field
 Cr : Set
 Bd : Pushout (Bd2a .Ball2.Bd) (Bd2b .Ball2.Bd) → Cr


data Tele : Set₁
Ball : Tele → Set₁
BallDom : Tele → Set

data Tele where
 tnil : Tele
 tcons : (t : Tele) (b1 b2 : Ball t) → Tele

Ball t = Σ[ Cr ∈ Set ] (BallDom t → Cr)
BallDom tnil = Void
BallDom (tcons t b1 b2) = Pushout (b1 .snd) (b2 .snd)

-- Ball tnil = Σ[ Cr ∈ Set ] void → Cr -- just a set, ideally Unit
-- Ball (tcons tnil b1 b2) = Σ[ Cr ∈ Set ] (b1 .fst + .b2 fst) → Cr  -- a set with two points


--------------------------------------------------------------------------------
-- postulate
--  -- paths of unbounded length
--  _⇒_ : {A : Set} (a a' : A) → Set

-- module _ (A : Set) where
--  data Tele : Set
--  Ball : Tele → Set

--  data Tele where
--   tnil : Tele
--   tcons : (t : Tele) (b1 b2 : Ball t) → Tele
--  Ball tnil = A
--  Ball (tcons t src tgt) = src ⇒ tgt

-- postulate
--  isFull : {A : Set} (t : Tele A) (b : Ball A t) → Set -- is a prop

-- -- Ball0 : Set
-- -- Ball0 = Unit

-- -- Sphere0 : Set
-- -- Sphere0 = Unit

-- -- record Ball1 : Set₁ where field
-- --  A : Set
-- --  a0 a1 : A
-- --  path : a0 ⇒ a1
-- --  full : isFull (tcons tnil a0 a1) path

-- -- Sphere1 : Set₁
-- -- Sphere1 = Ball1 × Ball1

-- -- record Ball2 (s1 : Sphere1) : Set₁ where field
-- --  A : Set
-- --  a0 a1 : A
-- --  path : a0 ⇒ a1
-- --  full : isFull (tcons tnil a0 a1) path

-- record GoodEdge1 : Set₁ where constructor mkGoodEdge ; field
--  A : Set
--  a0 a1 : A
--  path : a0 ⇒ a1
--  full : isFull (tcons tnil a0 a1) path

-- postulate
--  cell1 : GoodEdge1

-- module _ (ge1 : two → GoodEdge1) where
--  postulate
--   merged1 : Set -- pushout of ge1

--  record GoodEdge2 : Set₁ where constructor mkGoodEdge2 ; field
--   A : Set
--   a0 a1 : A
--   p0 p1 : a0 ⇒ a1
--   path : p0 ⇒ p1
--   full : isFull (tcons (tcons tnil a0 a1) p0 p1) path

--  postulate
--   cell2 : GoodEdge2
--   bd2 : merged1 → cell2 .GoodEdge2.A
