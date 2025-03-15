{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Functions.Embedding
open import Function.Base

module ParametricityViaParametricity where

module Param (S : Set) where
 postulate
  M : Set
  !r : M
  !a : S → M

 module _ (R : Set) (A : S → Set) (p : R → (s : S) → A s) where
  postulate
   Gel : (μ : M) → Set

   Gelβr : Gel !r ≡p R
   {-# REWRITE Gelβr #-}

   Gelβa : (s : S) → Gel (!a s) ≡p A s
   {-# REWRITE Gelβa #-}

 -- Now for the stuff that actually uses parametricity
 postulate
  related : (s : S) (T : M → Set) (xr : T !r) (xa : T (!a s)) → Set
  param : (s : S) (T : M → Set) (x : (μ : M) → T μ) → related s T (x !r) (x (!a s))

  related/K : (s : S) (D : Set) (xr xa : D) → related s (λ μ → D) xr xa ≡ (xr ≡ xa)

  related/Gp : (s : S) (R : Set) (A : S → Set) (p : R → (s : S) → A s) (xr : R) (xa : A s)
               → related s (Gel R A p) xr xa ≡p (p xr s ≡ xa)
  {-# REWRITE related/Gp #-}

  related/→ : (s : S) (A1 A2 : M → Set) (fr : A1 !r → A2 !r) (fa : A1 (!a s) → A2 (!a s))
               → related s (λ μ → A1 μ → A2 μ) fr fa ≡ ((xr : A1 !r) (xa : A1 (!a s)) → related s A1 xr xa → related s A2 (fr xr) (fa xa))

module Thm where
 S = Unit
 open Param S
 module _ (idf : (X : Set) → X → X) (Y : Set) (y : Y) where

  R = Unit
  A : S → Set
  A _ = Y
  p : R → (s : S) → A s
  p _ _ = y

  G : M → Set
  G = Gel R A p

  pivot : (μ : M) → G μ → G μ
  pivot μ = idf (G μ)

  thm : (s : Unit) (xr : R) → p (idf R xr) s ≡ idf (A s) (p xr s)
  thm s xr = transport (related/→ s G G (pivot !r) (pivot (!a s))) (param s (λ μ → G μ → G μ) pivot)
                            xr (p xr s) refl

  thm' : y ≡ idf Y y
  thm' = thm tt tt

module Thm2 (S : Set) where
 open Param S
 module _ (cnf : (X : Set) → (X → X) → (X → X)) (R : Set) (A : S → Set) (p : R → (s : S) → A s) where
   G : M → Set
   G = Gel R A p

   pfam : M → Set
   pfam μ = (G μ → G μ) → (G μ → G μ)

   ffam : M → Set
   ffam μ = (G μ → G μ)

   pivot : (μ : M) → pfam μ
   pivot μ = cnf (G μ)

   lemma1 : (s : S) → related s pfam (pivot !r) (pivot (!a s))
   lemma1 s = param s pfam pivot

   lemma2 : (s : S)
      (fr : ffam !r) (fa : ffam (!a s)) →
       related s ffam fr fa →
       related s ffam (pivot !r fr) (pivot (!a s) fa)
   lemma2 s = transport (related/→ s ffam ffam (pivot !r) (pivot (!a s))) (lemma1 s)

   lemma3 : (s : S)
      (fr : ffam !r) (fa : ffam (!a s)) →
       (((xr : R) (xa : A s) → related s G xr xa → related s G (fr xr) (fa xa))) →
       related s ffam (pivot !r fr) (pivot (!a s) fa)
   lemma3 s fr fa rr = lemma2 s fr fa (transport (sym (related/→ s G G fr fa)) rr)

   lemma4 : (s : S)
      (fr : R → R) (fa : A s → A s) →
       (((xr : R) (xa : A s) → related s G xr xa → related s G (fr xr) (fa xa))) →
       ((yr : R) (ya : A s) → related s G yr ya → related s G (cnf R fr yr) (cnf (A s) fa ya))
   lemma4 s fr fa rr = transport (related/→ s G G (pivot !r fr) (pivot (!a s) fa)) (lemma3 s fr fa rr)

   lemma5 : (s : S)
      (succr : R → R) (succa : A s → A s) →
       (succpres : ((xr : R) (xa : A s) → p xr s ≡ xa → p (succr xr) s ≡ (succa xa))) →
       (zr : R) → p (cnf R succr zr) s ≡ cnf (A s) succa (p zr s)
   lemma5 s succr succa succpres zr = lemma4 s succr succa succpres zr (p zr s) refl

   lemma6b : (s : S) (succr : R → R) (succa : A s → A s) →
           ((xr : R) → p (succr xr) s ≡ (succa (p xr s)))
        →  ((xr : R) (xa : A s) → p xr s ≡p xa → p (succr xr) s ≡ (succa xa))
   lemma6b s succr succa k xr .(p xr s) reflp = k xr

   lemma6 : (s : S)
       (succr : R → R) (succa : A s → A s) →
       (succpres : ((xr : R) → p (succr xr) s ≡ (succa (p xr s)))) →
       (zr : R) → p (cnf R succr zr) s ≡ cnf (A s) succa (p zr s)
   lemma6 s succr succa succpres = lemma5 s succr succa (λ xr xa pp → lemma6b s succr succa succpres xr xa (pathToEq pp))
