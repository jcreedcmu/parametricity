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

module SingleBackingSet where

data Void : Set where

abort : (A : Set) → Void → A
abort A ()

data Unit {ℓ : Level} : Set ℓ where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

data Tele : Set₁
BallOver : (Cr : Set) (t : Tele) → Set
record Ball (t : Tele) : Set₁
extract : Tele → Set

BallOver Cr t = Cr → extract t

data Tele where
 tnil : Set → Tele
 tcons : (t : Tele) (dom cod : Ball t) → Tele

record Ball t where constructor mkBall ; field
 Cr : Set
 Bd : BallOver Cr t

extract (tnil A) = A
extract (tcons t dom cod) = extract t

mergeTele : (t1 t2 : Tele) (B : Set) (B1 : BallOver B t1) (B2 : BallOver B t2) → Tele
mergeTele = {!!}

data Composable : Tele → Tele → Tele → Set₁ where
  zcomp : {t1 t2 t3 : Tele} (A B C : Set)
          (A1 : BallOver A t1) (A3 : BallOver A t3)
          (B1 : BallOver B t1) (B2 : BallOver B t2)
          (C2 : BallOver C t2) (C3 : BallOver C t3)
      → Composable
        (tcons t1 (mkBall A A1) (mkBall B B1))
        (tcons t2 (mkBall B B2) (mkBall C C2))
        (tcons t3 (mkBall A A3) (mkBall C C3))
