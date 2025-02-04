{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module SimpleSyntax where

postulate
 ♯ : ∀ {ℓ} → Type ℓ → Type ℓ
 ι : ∀ {ℓ} {A : Type ℓ} → A → ♯ A
module Param {ℓ ℓ' ℓ'' : Level}
         (A : Type ℓ) (S : Type ℓ') (B : S → Type ℓ'')
         (M : A → (s : S) → B s)
 where
 postulate
  Gel : ♯ S → Type ℓ''
  Gel-ι : (s : S) → Gel (ι s) ≡p B s
  {-# REWRITE Gel-ι #-}
  gel : (a : A) (s' : ♯ S) → Gel s'
  gel-ι : (a : A) (s : S) → gel a (ι s) ≡p M a s
  {-# REWRITE gel-ι #-}
  ungel : ((s' : ♯ S) → Gel s') → A

  gelβ : (a : A) → ungel (λ s' → gel a s') ≡p a
  {-# REWRITE gelβ #-}
  gelη : (f : (s' : ♯ S) → Gel s') (s' : ♯ S) → gel (ungel f) s' ≡p f s'
  {-# REWRITE gelη #-}

 H : (f : (s' : ♯ S) → Gel s') (s : S) → M (ungel f) s ≡ f (ι s)
 H f s = sym (eqToPath (gel-ι (ungel f) s))

data two : Type where
 t0 t1 : two

data unit : Type where
 * : unit

module RelThm (M : (X : Type) → X → X) (R : Type) (A : two → Type) (f : R → (t : two) → A t) (r : R) where
 open Param R two A f

 r' : R
 r' = ungel (λ s' → M (Gel s') (gel r s'))

 lemma : (t : two) → f r' t ≡ M (A t) (f r t)
 lemma = H (λ s' → M (Gel s') (gel r s'))

module Exact (M : (X : Type) → X → X) (A B : Type) (a : A) where
 myf : A → (t : two) → A
 myf a' t0 = a'
 myf a' t1 = a

 combine : a ≡ M A a
 combine = RelThm.lemma M A (λ _ → A) myf a t1


module Exact2 (M : (X : Type) → X → X) (A : Type) (a : A) where
 open Param A unit (λ _ → A) (λ _ _ → a )

 thm : a ≡ M A a
 thm = H (λ s' → M (Gel s') (gel a s')) *

module RelThmIx
    (M : (X : Type) → X → X)
    (A B : Type) (R : A → B → Type)
    (a : A) (b : B) (r : R a b)
    where

 Total : Type
 Total = Σ[ a ∈ A ] Σ[ b ∈ B ] R a b

 p : Total
 p = a , (b , r)

 Bd : two → Type
 Bd t0 = A
 Bd t1 = B

 proj : Total → (t : two) → Bd t
 proj (a , b , r) t0 = a
 proj (a , b , r) t1 = b

 open Param Total two Bd proj

 p' : Total
 p' = ungel (λ s' → M (Gel s') (gel p s'))

 lemma : (t : two) → proj p' t ≡ M (Bd t) (proj p t)
 lemma = H (λ s' → M (Gel s') (gel p s'))

 thm : R (M A a) (M B b)
 thm = subst (λ z → R (M A a) z) (lemma t1) (subst (λ z → R z (proj p' t1)) (lemma t0) (snd (snd p')))

module Practice
    (S : Type)
    (C1 C2 : Type) -- total spaces
    (D1 D2 : S → Type) -- boundaries
    (f1 : C1 → (s : S) → D1 s) -- structure map of the relations
    (f2 : C2 → (s : S) → D2 s)
    where
 record Relhom : Type where
  field
   totalMap : C1 → C2
   bdMap : (s : S) → D1 s → D2 s
   pbck : (c1 : C1) (s : S) → f2 (totalMap c1) s ≡ bdMap s (f1 c1 s)

 bdMapf1 : Relhom × C1 → (s : S) → (D1 s → D2 s) × D1 s
 bdMapf1 (rh , c1) s = (Relhom.bdMap rh s) , (f1 c1 s)

 module Pf = Param Relhom S (λ s → D1 s → D2 s) Relhom.bdMap
 module Pf1 = Param (Relhom × C1) S (λ s → (D1 s → D2 s) × D1 s) bdMapf1

 module P1 = Param C1 S (λ s → D1 s) f1
 module P2 = Param C2 S (λ s → D2 s) f2

 evalMap : (s' : ♯ S) → Pf.Gel s' × P1.Gel s' → P2.Gel s'
 evalMap = {!!}

module RelThmHigher
    (M : (X : Type) → (X → X) → X)
    (Total : Type)
    (Bd : two → Type)
    (proj : Total → (t : two) → Bd t)
    (f : (t : two) → Bd t → Bd t) -- a pair of functions...
    (f~ : (r : Total) → Total) -- ...for which there is evidence that they are related...
    (f~p : (r : Total) (t : two) → f t (proj r t) ≡ proj (f~ r) t) -- ...which really is a relation homomorphism
    where
 -- the theorem I want to prove at this point is there
 -- exists an p' : Total whose boundary is (M (Bd t0) (f t0), M (Bd t1) (f t1))

 open Param Total two Bd proj

 cvt-f : (s' : ♯ two) → Gel s' → Gel s'
 cvt-f s' g = gel {!!} s'

 p' : Total
 p' = ungel (λ s' → M (Gel s') (cvt-f s'))

 thm : (t : two) → proj p' t ≡ M (Bd t) (f t)
 thm = {!!}
