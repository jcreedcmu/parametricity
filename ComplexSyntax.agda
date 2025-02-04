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

module ComplexSyntax {ℓ0 : Level} (S : Type ℓ0) where

postulate
 ♯ : ∀ {ℓ} → Type ℓ → Type ℓ
 ι : ∀ {ℓ} {A : Type ℓ} → A → ♯ A


record Rel (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ ⊔ ℓ' ⊔ ℓ0)) where
 constructor mkRel
 field
  rA : Type ℓ
  rB : S → Type ℓ'
  rM : rA → (s : S) → rB s

record Hom {ℓ ℓ' : Level} (R1 R2 : Rel ℓ ℓ') : Type (ℓ ⊔ ℓ' ⊔ ℓ0)  where -- more level flexibility here?
 constructor mkHom
 open Rel
 field
  fA : R1 .rA → R2 .rA
  fB : (s : S) → R1 .rB s → R2 .rB s
  f= : (s : S) (a : R1 .rA) → R2 .rM (fA a) s  ≡ fB s (R1 .rM a s)

module GelType {ℓ ℓ' : Level} (R : Rel ℓ ℓ') where
 open Rel
 postulate
  Gel : ♯ S → Type ℓ'
  Gel-ι : (s : S) → Gel (ι s) ≡p (R .rB) s
  {-# REWRITE Gel-ι #-}

module GelOps1 {ℓ ℓ' ℓ'' : Level}
  (A : Type ℓ) (B : S → Type ℓ'')
  (M : A → (s : S) → B s) where
 open GelType (mkRel A B M)
 postulate

  -- I think gel and ungel can be implemented in terms of gel2 and ungel2 below
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

module GelOps2 {ℓ ℓ' : Level} (R1 R2 : Rel ℓ ℓ') where -- more level flexibility here?
  open Rel
  open Hom
  open GelType

  postulate
   gel2 : (h : Hom R1 R2) (s' : ♯ S) → Gel R1 s' → Gel R2 s'
   ungel2 : ((s' : ♯ S) → Gel R1 s' → Gel R2 s') → Hom R1 R2
   gel2-ι : (h : Hom R1 R2) (N : S) → gel2 h (ι N) ≡p h .fB N
   gel2β : (h : Hom R1 R2) → ungel2 (gel2 h) ≡p h
   gel2η : (g : (s' : ♯ S) → Gel R1 s' → Gel R2 s') → gel2 (ungel2 g) ≡p g
