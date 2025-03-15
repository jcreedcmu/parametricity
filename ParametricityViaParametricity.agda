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

module Shape (S : Set) where
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
  param : (s : S) (T : M → Set) (x : (μ : M) → T μ)→ related s T (x !r) (x (!a s))

  related/K : (s : S) (D : Set) (xr xa : D) → related s (λ μ → D) xr xa ≡ (xr ≡ xa)
  related/G : (s : S) (R : Set) (A : S → Set) (p : R → (s : S) → A s) (xr : R) (xa : A s)
               → related s (Gel R A p) xr xa ≡ (p xr s ≡ xa)
  related/→ : (s : S) (A1 A2 : M → Set) (fr : A1 !r → A2 !r) (fa : A1 (!a s) → A2 (!a s))
               → related s (λ μ → A1 μ → A2 μ) fr fa ≡ ((xr : A1 !r) (xa : A1 (!a s)) → related s A1 xr xa → related s A2 (fr xr) (fa xa))

module Thm where
 S = Unit
 open Shape S
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
  thm s xr = transport (related/G s R A p (idf R xr) (idf (A s) (p xr s)))
                         (transport (related/→ s G G (pivot !r) (pivot (!a s))) (param s (λ μ → G μ → G μ) pivot)
                            xr (p xr s) (transport (sym (related/G s R A p xr (p xr s))) refl))

  thm' : y ≡ idf Y y
  thm' = thm tt tt
