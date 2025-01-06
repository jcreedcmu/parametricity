{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base
import Interval.Gel

{-
 - This is an attempt to factor out some convenient lemmas for functoriality
 -}
module Interval.ThreePush where

module _ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) (C : A → B → Set ℓ) where -- needs more level flexibility? idk

 record Threep : Set ℓ where
  constructor thr
  field
   fa : A
   fb : B
   fc : C fa fb

module _ {ℓ : Level} (A A' : Set ℓ) (B : Set ℓ) (C : A → B → Set ℓ) -- needs more level flexibility? idk
         (fiso : A' ≅ A)
         where
 private
  f = fiso .fst
  fEq = fiso .snd
  finv = invIsEq fEq

  fore : Threep A B C → Threep A' B (λ a b → C (f a) b)
  fore (thr fa fb fc) = thr (finv fa) fb (subst (λ a → C a fb) (sym (secIsEq fEq fa)) fc)

  back : Threep A' B (λ a b → C (f a) b) → Threep A B C
  back (thr fa fb fc) = thr (f fa) fb fc

  sect-lemma : (a : A') (b : B) (c : C (f a) b) →
             PathP (λ i → (C (f (retIsEq fEq a i)) b))
                   (subst (λ a → C a b) (sym (secIsEq fEq (f a))) c)
                   c
  sect-lemma a b c = toPathP⁻ (λ j → transport (λ i → C (commPathIsEq fEq a j (~ i) ) b) c)

  sect : (t : Threep A' B (λ a b → C (f a) b)) → fore (back t) ≡ t
  sect (thr fa fb fc) i = thr (retIsEq fEq fa i) fb (sect-lemma fa fb fc i)

  retr : (t : Threep A B C) → back (fore t) ≡ t
  retr (thr fa fb fc) i = thr (secIsEq fEq fa i) fb (transp (λ j → C (secIsEq fEq fa (i ∨ ~ j)) fb) i fc)

 congA : Threep A B C ≅ Threep A' B (λ a b → C (f a) b)
 congA = isoToEquiv (iso fore back sect retr)

module _ {ℓ : Level} (A : Set ℓ) (B B' : Set ℓ) (C : A → B → Set ℓ) -- needs more level flexibility? idk
         (fiso : B' ≅ B)
         where
 private
  f = fiso .fst
  fEq = fiso .snd
  finv = invIsEq fEq

  fore : Threep A B C → Threep A B' (λ a b → C a (f b))
  fore (thr fa fb fc) = thr fa (finv fb) (subst (λ b → C fa b) (sym (secIsEq fEq fb)) fc)

  back : Threep A B' (λ a b → C a (f b)) → Threep A B C
  back (thr fa fb fc) = thr fa (f fb) fc

  sect-lemma : (a : A) (b : B') (c : C a (f b)) →
             PathP (λ i → (C a (f (retIsEq fEq b i))))
                   (subst (λ b → C a b) (sym (secIsEq fEq (f b))) c)
                   c
  sect-lemma a b c = toPathP⁻ (λ j → transport (λ i → C a (commPathIsEq fEq b j (~ i) )) c)

  sect : (t : Threep A B' (λ a b → C a (f b))) → fore (back t) ≡ t
  sect (thr fa fb fc) i = thr fa (retIsEq fEq fb i) (sect-lemma fa fb fc i)

  retr : (t : Threep A B C) → back (fore t) ≡ t
  retr (thr fa fb fc) i = thr fa (secIsEq fEq fb i) (transp (λ j → C fa (secIsEq fEq fb (i ∨ ~ j))) i fc)

 congB : Threep A B C ≅ Threep A B' (λ a b → C a (f b))
 congB = isoToEquiv (iso fore back sect retr)
