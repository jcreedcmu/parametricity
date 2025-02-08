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

module Telescopes where

data Void : Set where

abort : (A : Set) → Void → A
abort A ()

data Unit {ℓ : Level} : Set ℓ where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

module Hide where
 record Tele : Set₂ where constructor mkTele ; field
  -- the type of weights
  Wt : Set₁
  -- the realization of the telescope for some particular weight vector
  Re : Wt → Set
  -- maps from one weight vector to another?
  Hom : Wt → Wt → Set

 record Ball (t : Tele) : Set₁ where open Tele ; field
  -- The carrier of the ball
  Cr : Set
  -- The weight vector of the ball - how much it uses each element of the telescope
  wv : Wt t
  -- The boundary map of the ball
  ∂ : Re t wv → Cr

 open Tele
 open Ball

 nilTele : Tele
 nilTele = mkTele Unit (λ _ → Void) (λ _ _ → Unit)

 consTele : (t : Tele) (b : Ball t) → Tele
 consTele t b = mkTele
     (Σ[ ω ∈ Wt t ] Σ[ ω' ∈ Type ] Hom t (wv b) ω)
     doRe
     {!!} where
   doRe : (Σ[ ω ∈ Wt t ] Σ[ ω' ∈ Type ] Hom t (wv b) ω) → Set
   doRe = {!!}

module Usage where
 -- Forward declarations for mutual recursion:
 data Tele : Set
 data SubTele : Tele → Set
 data subset : {t : Tele} → SubTele t → SubTele t → Set

 -- Definitions:
 data Tele where
  tnil : Tele
  tcons : (t : Tele)  (b : SubTele t) → Tele

 data SubTele where
  stnil : SubTele tnil
  stskip : (t : Tele) (st : SubTele t) (b : SubTele t) → SubTele (tcons t b)
  stuse : (t : Tele) (st : SubTele t) (b : SubTele t) → (subset b st) → SubTele (tcons t b)

 data subset where
  subnil : subset stnil stnil
  subskips : (t : Tele) (st st' : SubTele t) (b : SubTele t)
    → subset st st' → subset (stskip t st b) (stskip t st' b)
  subchange : (t : Tele) (st st' : SubTele t) (b : SubTele t) (σ' : subset b st')
    → subset st st' → subset (stskip t st b) (stuse t st' b σ')
  subuses : (t : Tele) (st st' : SubTele t) (b : SubTele t)
            (σ : subset b st) (σ' : subset b st')
    → subset st st' → subset (stuse t st b σ) (stuse t st' b σ')

module Usage2 where
 -- Forward declarations for mutual recursion:
 data Tele : Set₁
 data Ball : Tele → Set₁
 data over : {t : Tele} → Ball t → Set₁

 -- Definitions:
 data Tele where
  tnil : Tele
  tcons : (t : Tele) (b : Ball t) → Tele

 data Ball where
  stnil : Ball tnil
  stuse : (t : Tele) (b : Ball t) (X : Set) (ws : X → over b) → Ball (tcons t b)

 data over where

  -- wtnil : hom stnil stnil
  -- wtcons : (t : Tele) (st st' : Ball t) (b : Ball t) → {!!}
  -- wtskips : (t : Tele) (st st' : Ball t) (b : Ball t)
  --   → hom st st' → hom (stskip t st b) (stskip t st' b)
  -- wtchange : (t : Tele) (st st' : Ball t) (b : Ball t) (σ' : hom b st')
  --   → hom st st' → hom (stskip t st b) (stuse t st' b σ')
  -- wtuses : (t : Tele) (st st' : Ball t) (b : Ball t)
  --           (σ : hom b st) (σ' : hom b st')
  --   → hom st st' → hom (stuse t st b σ) (stuse t st' b σ')
