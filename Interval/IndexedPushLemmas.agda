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
Push-left-cong-equiv {ℓ1} {ℓ2} {ℓ3} {A = A} {A'} {C = C} f g eq = isoToEquiv (iso fore back {!!} {!!}) where
 fore : Push {A = A} f g → Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g
 fore (pinl a) = pinl (invIsEq (eq .snd) a)
 fore (pinr b) = pinr b
 fore (ppath c i) = ppath c i

 back : Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g → Push {A = A} f g
 back (pinl a) = pinl (funIsEq (eq .snd) a)
 back (pinr b) = pinr b
 back (ppath c i) = (ppath c ∙∙ refl ∙∙ λ j → pinl (secIsEq (eq .snd) (f c) (~ i ∨ ~ j))) i

 inv = invIsEq (eq .snd)
 sec = secIsEq (eq .snd)
 ret = retIsEq (eq .snd)

 sect : (g : Push {A = A'} (λ c → invIsEq (eq .snd) (f c)) g ) → fore (back g) ≡ g
 sect (pinl a) = λ i → pinl ((retIsEq (eq .snd) a) i)
 sect (pinr b) = λ i → pinr b
 sect (ppath c i)  = proof i where

   lemma3 : (eq : A ≅ A') (a : A) → Square (λ i → secIsEq (eq .snd) (funIsEq (eq .snd) a) i)
                  (λ _ → (funIsEq (eq .snd) a))
                  (λ i → (funIsEq (eq .snd) (retIsEq (eq .snd) a i)))
                  (λ _ → (funIsEq (eq .snd) a))
   lemma3 eq a = commSqIsEq (eq .snd) a


   betterInvEquiv' : {A B : Set} → (f : A → B) → ((b : B) → isContr (fiber f b)) → B ≅ A
   betterInvEquiv' f fibc = (λ b → fibc b .fst .fst) , -- <- this is f⁻¹
        record { equiv-proof = λ a → (f a , -- <-- this is f
                 cong fst (fibc (f a) .snd (a , refl))) , -- <-- this is ret for f, sec for f⁻¹
                 λ {(b , path) i → ((cong f (sym path) ∙ fibc b .fst .snd) i ) , {!!} } } -- <- this is sec for f, ret for f⁻¹
--
   betterInvEquiv : {A B : Set} → A ≅ B → B ≅ A
   betterInvEquiv (f , fise) = betterInvEquiv' f (fise .equiv-proof)

   check1 : (eq : A' ≅ A) → funIsEq (eq .snd) ≡ invIsEq (invEquiv eq .snd)
   check1 eq = refl

   check : (eq : A' ≅ A) → invIsEq (eq .snd) ≡ funIsEq (invEquiv eq .snd)
   check eq = refl

   check2 : (eq : A' ≅ A) → retIsEq (eq .snd) ≡ secIsEq (invEquiv eq .snd)
   check2 eq = refl

   check3 : (eq : A' ≅ A) → secIsEq (eq .snd) ≡ retIsEq (invEquiv eq .snd)
   check3 eq i a j = {!!}

   lemma2 : (eq : A' ≅ A) (a : A) → Square (λ i → retIsEq (eq .snd) (invIsEq (eq .snd) a) i)
                  (λ _ → (invIsEq (eq .snd) a))
                  (λ i → (invIsEq (eq .snd) (secIsEq (eq .snd) a i)))
                  (λ _ → (invIsEq (eq .snd) a))
   lemma2 eq a = {!eq .snd!}
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
