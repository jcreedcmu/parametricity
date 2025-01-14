{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
-- open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to aborti)
-- open import Cubical.Foundations.Equiv
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

module StrictEquiv2 where

-- here I'm trying to formalize Peter Lumsdaine's def'n from
-- https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/

infix 4 _≅_

record isEquiv {ℓ : Level} {A : Set ℓ} {B : Set ℓ} (f : A → B) : Set (ℓ-suc ℓ) where
 field
  R : A → B → Set ℓ
  g : B → A
  A-contr : (a : A) → isContr (Σ B (λ b → R a b))
  B-contr : (b : B) → isContr (Σ A (λ a → R a b))
  f-match : (a : A) → R a (f a)
  g-match : (b : B) → R (g b) b

_≅_ : {ℓ : Level} (A : Set ℓ) (B : Set ℓ) → Set (ℓ-suc ℓ)
A ≅ B = Σ (A → B) isEquiv

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅ B) where
 f = q .fst
 open isEquiv (q .snd)

 getFun : A → B
 getFun = f

 getInv : B → A
 getInv = g

 f-unmatch : {a : A} {b : B} → R a b → f a ≡ b
 f-unmatch {a} {b} r = cong fst (sym (A-contr a .snd (f a , f-match a)) ∙ (A-contr a .snd (b , r)))

 g-unmatch : {b : B} {a : A} → R a b → g b ≡ a
 g-unmatch {b} {a} r = cong fst (sym (B-contr b .snd (g b , g-match b)) ∙ B-contr b .snd (a , r))

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = f-unmatch (g-match b)

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = g-unmatch (f-match a)

 invert : B ≅ A
 invert = (g , record
                { R = λ b a → R a b
                ; g = f
                ; A-contr = B-contr
                ; B-contr = A-contr
                ; f-match = g-match
                ; g-match = f-match
                })

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅ B) where
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
