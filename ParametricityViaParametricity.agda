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
open import Function.Base

module ParametricityViaParametricity where

module _ (S : Set) where
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
  related : (s : S) (T : M → Set) (x : (μ : M) → T μ) → Set
  param : (s : S) (T : M → Set) (x : (μ : M) → T μ)→ related s T x

  related/K : (D : Set) (t : M → D) (s : S) → related s (λ μ → D) t ≡ (t !r ≡ t (!a s))
  related/G : (R : Set) (A : S → Set) (p : R → (s : S) → A s) (t : (μ : M) → Gel R A p μ)
              (s : S) → related s (Gel R A p) t ≡ (p (t !r) s ≡ t (!a s))
  related/→ : (A1 A2 : M → Set) (f : (μ : M) → A1 μ → A2 μ)
              (s : S) → related s (λ μ → A1 μ → A2 μ) f ≡ ((x : (μ : M) → A1 μ) → related s A1 x → related s A2 λ μ →  f μ (x μ))

 module _ (q : (X : Set) → X → X) (R : Set) (A : S → Set) (p : R → (s : S) → A s) where

  G : M → Set
  G = Gel R A p

  pivot : (μ : M) → G μ → G μ
  pivot μ = q (G μ)

  paramPivot : (s : S) → related s (λ μ → G μ → G μ) pivot
  paramPivot s = param s (λ μ → G μ → G μ) pivot

  paramPivot→ : (s : S) (x : (μ : M) → G μ) → related s G x → related s G (λ μ → pivot μ (x μ))
  paramPivot→ s = transport (related/→ G G pivot  s) (paramPivot s)
