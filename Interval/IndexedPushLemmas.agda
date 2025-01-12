{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection
open import Interval.Discreteness

module Interval.IndexedPushLemmas where

-- data Push {ℓ0 ℓ1 ℓ2 ℓ3 : Level}
--           {T : Type ℓ0} {A : T → Type ℓ1} {B : T → Type ℓ2} {C : T → Type ℓ3}
--           (f : {t : T} → C t → A t) (g : {t : T} → C t → B t)
--           : T → Set (ℓ0 ⊔ ℓ1 ⊔ ℓ2 ⊔ ℓ3) where
--   pinl : {t : T} (a : A t) → Push f g t
--   pinr : {t : T} (b : B t) → Push f g t
--   ppath : {t : T} (c : C t) → pinr (g c) ≡ pinl (f c)

-- Push-left-cong-equiv :
--           {ℓ0 ℓ1 ℓ2 ℓ3 : Level}
--           {T : Type ℓ0} {A : T → Type ℓ1} {A' : T → Type ℓ1}
--           {B : T → Type ℓ2} {C : T → Type ℓ3}
--           (f : {t : T} → C t → A t) (g : {t : T} → C t → B t)
--           (eq : {t : T} → A' t ≅ A t)
--           → (t : T) → Push {A = A} f g t ≅ Push {A = A'} (λ {t} c → invIsEq (eq .snd) (f c)) g t
-- Push-left-cong-equiv {A = A} {A'} f g eq t = isoToEquiv (iso fore back {!!} {!!}) where
--  fore : Push {A = A} f g t → Push {A = A'} (λ {t} c → invIsEq (eq .snd) (f c)) g t
--  fore (pinl a) = pinl (invIsEq (eq .snd) a)
--  fore (pinr b) = pinr b
--  fore (ppath c i) = ppath c i

--  back : Push {A = A'} (λ {t} c → invIsEq (eq .snd) (f c)) g t → Push {A = A} f g t
--  back (pinl a) = pinl (funIsEq (eq .snd) a)
--  back (pinr b) = pinr b
--  back (ppath c i) = (ppath c ∙ λ j → pinl (secIsEq (eq .snd) (f c) (~ i ∨ ~ j))) i

--  sect : (g : Push {A = A'} (λ {t} c → invIsEq (eq .snd) (f c)) g t) → fore (back g) ≡ g
--  sect (pinl a) i = pinl ((retIsEq (eq .snd) a) i)
--  sect (pinr b) i = pinr b
--  sect (ppath c i) = {!!}

data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B)
          : Set (ℓ1 ⊔ ℓ2 ⊔ ℓ3) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  ppath : (c : C) → pinr (g c) ≡ pinl (f c)

Push-left-cong-equiv :
          {ℓ1 ℓ2 ℓ3 : Level}
          {A A' : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B)
          (eq : A' ≅ A)
          → Push {A = A} f g ≅ Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g
Push-left-cong-equiv {ℓ1} {ℓ2} {ℓ3} {A = A} {A'} f g eq = isoToEquiv (iso fore back {!!} {!!}) where
 fore : Push {A = A} f g → Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g
 fore (pinl a) = pinl (invIsEq (eq .snd) a)
 fore (pinr b) = pinr b
 fore (ppath c i) = ppath c i

 back : Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g → Push {A = A} f g
 back (pinl a) = pinl (funIsEq (eq .snd) a)
 back (pinr b) = pinr b
 back (ppath c i) = (ppath c ∙∙ refl ∙∙ λ j → pinl (secIsEq (eq .snd) (f c) (~ i ∨ ~ j))) i

 sect : (g : Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g ) → fore (back g) ≡ g
 sect (pinl a) = λ i → pinl ((retIsEq (eq .snd) a) i)
 sect (pinr b) = λ i → pinr b
 sect (ppath c i)  = proof i where
   foo  : Set (ℓ1 ⊔ ℓ2 ⊔ ℓ3)
   foo = PathP (λ i → fore (back (ppath c i)) ≡ ppath c i)
        (λ _ → pinr (g c))
        (λ i → pinl ((retIsEq (eq .snd) (invIsEq (eq .snd) (f c))) i))
   proof : foo
   proof = {!!}

 retr : (g : Push {A = A} f g) → back (fore g) ≡ g
 retr (pinl a) i = pinl ((secIsEq (eq .snd) a) i)
 retr (pinr b) i = pinr b
 retr (ppath c i) j = hcomp (λ k → λ {
   (i = i0) → ppath c (~ k) ;
   (j = i0) → doubleCompPath-filler (ppath c) refl (λ j → pinl (secIsEq (eq .snd) (f c) (~ i ∨ ~ j))) k i  ;
   (i = i1) → pinl (secIsEq (eq .snd) (f c) (j ∨ ~ k)) ;
   (j = i1) → ppath c (i ∨ ~ k ) })
  (pinl (f c))
