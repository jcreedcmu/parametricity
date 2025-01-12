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
--  back (ppath c i) = (ppath c ∙ λ j → pinl (Isec eq (f c) (~ i ∨ ~ j))) i

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

open Iso using () renaming (fun to Ifun ; inv to Iinv ; rightInv to Isec ; leftInv to Iret)

Push-left-cong-equiv :
          {ℓ1 ℓ2 ℓ3 : Level}
          {A A' : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B)
          (eq : Iso A' A)
          → Push {A = A} f g ≅ Push {A = A'} (λ c → Iso.inv eq (f c)) g
Push-left-cong-equiv {ℓ1} {ℓ2} {ℓ3} {A = A} {A'} {C = C} f g eq = isoToEquiv (iso fore back {!!} {!!}) where
 fore : Push {A = A} f g → Push {A = A'} (λ c → Iso.inv eq (f c)) g
 fore (pinl a) = pinl (Iso.inv eq a)
 fore (pinr b) = pinr b
 fore (ppath c i) = ppath c i

 back : Push {A = A'} (λ c → Iso.inv eq (f c)) g → Push {A = A} f g
 back (pinl a) = pinl (Ifun eq a)
 back (pinr b) = pinr b
 back (ppath c i) = (ppath c ∙∙ refl ∙∙ λ j → pinl (Isec eq (f c) (~ i ∨ ~ j))) i

 inv = Iso.inv eq
 sec = Isec eq
 ret = Iret eq

 sect : (g : Push {A = A'} (λ c → Iso.inv eq (f c)) g ) → fore (back g) ≡ g
 sect (pinl a) = λ i → pinl ((ret a) i)
 sect (pinr b) = λ i → pinr b
 sect (ppath c i)  = proof i where

   lemma3 : (eq : Iso A A') (a : A) → Square (λ i → Isec eq (Ifun eq a) i)
                  (λ _ → (Ifun eq a))
                  (λ i → (Ifun eq (Iret eq a i)))
                  (λ _ → (Ifun eq a))
   lemma3 eq a i j = {!commSqIsEq (isoToEquiv eq .snd) a i j!}

   lemma2 : (eq : Iso A' A) (a : A) → Square (λ i → Iret eq (Iinv eq a) i)
                  (λ _ → (Iso.inv eq a))
                  (λ i → (Iso.inv eq (Isec eq a i)))
                  (λ _ → (Iso.inv eq a))
   lemma2 eq a = lemma3 (invIso eq) a
  -- commSqIsEq : ∀ a → Square (secIsEq (f a)) refl (cong f (retIsEq a)) refl
  -- commSqIsEq a i = equivF .equiv-proof (f a) .snd (a , refl) i .snd
   lemma : (a : A) → Square (λ i → ret (inv a) i)
                  (λ _ → (inv a))
                  (λ i → (inv (sec a i)))
                  (λ _ → (inv a))
   lemma a j k = lemma2 eq a j k


   proof : Square
        (λ _ → pinr (g c))
        (λ i → pinl (ret (inv (f c)) i))
        (λ i → fore ((ppath c ∙∙ refl ∙∙ λ j → pinl (sec (f c) (~ i ∨ ~ j))) i))
        (ppath c)
   proof i j = hcomp (λ k → λ {
    (i = i0) → ppath c (~ k) ;
    (j = i0) → fore ((doubleCompPath-filler (ppath c) refl (λ j → pinl (sec (f c) (~ i ∨ ~ j))) k i )) ;
    (i = i1) → pinl (lemma (f c) (~ k) j) ;
    (j = i1) → ppath c (i ∨ ~ k)
    }) (pinl (inv (f c)))


-- pinl (commSqIsEq (invEquiv eq .snd) (f c) (~ k) j)
 retr : (g : Push {A = A} f g) → back (fore g) ≡ g
 retr (pinl a) i = pinl (sec a i)
 retr (pinr b) i = pinr b
 retr (ppath c i) j = hcomp (λ k → λ {
   (i = i0) → ppath c (~ k) ;
   (j = i0) → doubleCompPath-filler (ppath c) refl (λ j → pinl (sec (f c) (~ i ∨ ~ j))) k i  ;
   (i = i1) → pinl (sec (f c) (j ∨ ~ k)) ;
   (j = i1) → ppath c (i ∨ ~ k ) })
  (pinl (f c))
