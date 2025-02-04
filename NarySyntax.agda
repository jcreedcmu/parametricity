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

module NarySyntax where
module Arity {ℓ0 : Level} (S : Type ℓ0) where
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

 module GelOps {ℓ ℓ' : Level}
   (A : Type ℓ) (B : S → Type ℓ')
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

 module ProductRelation {ℓ ℓ' ℓ'' : Level} (Z : Set ℓ) (Rs : Z → Rel ℓ' ℓ'') where
  open Rel

 module GelOpsN {ℓ ℓ' ℓ'' : Level} (Z : Set ℓ) (Rs : Z → Rel ℓ' ℓ'') (R0 : Rel (ℓ ⊔ ℓ') (ℓ ⊔ ℓ'')) where
  open Rel
  open Hom
  open GelType

  prodR : Rel (ℓ ⊔ ℓ') (ℓ ⊔ ℓ'')
  prodR = mkRel ((z : Z) → Rs z .rA) (λ s → (z : Z) → Rs z .rB s) λ v s z → Rs z .rM (v z) s

  postulate
   gelN : (h : Hom prodR R0) (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s'
   ungelN : ((s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') → Hom prodR R0
   gelN-ι : (h : Hom prodR R0) (N : S) → gelN h (ι N) ≡p h .fB N
   {-# REWRITE gelN-ι #-}
   gelNβ : (h : Hom prodR R0) → ungelN (gelN h) ≡p h
   {-# REWRITE gelNβ #-}
   gelNη : (g : (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') → gelN (ungelN g) ≡p g
   {-# REWRITE gelNη #-}

  HN : (f : (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') (s : S) → ungelN f .fB s ≡ (λ s' → f (ι s) s')
  HN f s = sym (eqToPath (gelN-ι (ungelN f) s))

data Unit {ℓ : Level} : Type ℓ where
 ⋆ : Unit

module RelThmHigher
    (S : Type)
    (M : (X : Type) → (X → X) → (X → X))
    (Total : Type)
    (Bd : S → Type)
    (proj : Total → (s : S) → Bd s)
    (succ : (s : S) → Bd s → Bd s) -- a pair of functions...
    (succ~ : (r : Total) → Total) -- ...for which there is evidence that they are related...
    (succ~p : (s : S) (r : Total) → proj (succ~ r) s ≡ succ s (proj r s)) -- ...which really is a relation homomorphism
    (zero~ : Total)
    where
 -- the theorem I want to prove at this point is there
 -- exists an p' : Total whose boundary is (M (Bd t0) (succ t0), M (Bd t1) (succ t1))
 open Arity S
 open GelType (mkRel Total Bd proj)
 open GelOps Total Bd proj
 open GelOpsN Unit (λ _ → mkRel Total Bd proj) (mkRel Total Bd proj)

 succ-gel : (s' : ♯ S) → Gel s' → Gel s'
 succ-gel s' = (λ c → gelN (Arity.mkHom (λ z → succ~ (z ⋆)) (λ s b → succ s (b ⋆)) λ s a → succ~p s (a ⋆)) s' (λ _ → c))

 x-gel : (s' : ♯ S) → Gel s'
 x-gel s' = gel zero~ s'

 out-gel : (s' : ♯ S) → Gel s'
 out-gel s' = M (Gel s') (succ-gel s') (x-gel s')

 out : Total
 out = ungel out-gel

 thm : (s : S) → proj out s ≡ M (Bd s) (succ s) (proj zero~ s)
 thm s = H out-gel s
