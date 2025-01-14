{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
-- open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module StrictEquiv where

infix 4 _≅_

record _≅_ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set (ℓ-suc ℓ) where
 field
  R : Set ℓ
  f : R → A
  g : R → B
  f-contr : (a : A) → isContr (fiber f a)
  g-contr : (b : B) → isContr (fiber g b)

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅ B) where
 open _≅_ q

 getFun : A → B
 getFun a = g (f-contr a .fst .fst)

 getInv : B → A
 getInv b = f (g-contr b .fst .fst)

 getSecLemma : (r : R) → (f-contr (f r) .fst .fst) ≡ r
 getSecLemma r i = f-contr (f r) .snd (r , refl) i .fst

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = (cong (g) (getSecLemma (g-contr b .fst .fst))) ∙ (g-contr b .fst .snd)

 getRetLemma : (r : R) → (g-contr (g r) .fst .fst) ≡ r
 getRetLemma r i = g-contr (g r) .snd (r , refl) i .fst

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = (cong (f) (getRetLemma (f-contr a .fst .fst))) ∙ (f-contr a .fst .snd)

 invert : B ≅ A
 invert = record { R = R ; f = g ; g = f ; f-contr = g-contr ; g-contr = f-contr }

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅ B) where
 open _≅_

 invert-strict-inv : invert (invert q) ≡ q
 invert-strict-inv = refl

 invertPresFun : getFun q ≡ getInv (invert q)
 invertPresFun = refl

 invertPresInv : getInv q ≡ getFun (invert q)
 invertPresInv = refl

 invertPresRet : getRet q ≡ getSec (invert q)
 invertPresRet = refl

 invertPresSec : getSec q ≡ getRet (invert q)
 invertPresSec = refl
