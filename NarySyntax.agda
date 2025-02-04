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

 module GelOps2 {ℓ ℓ' : Level} (R1 R2 : Rel ℓ ℓ') where -- more level flexibility here?
   open Rel
   open Hom
   open GelType

   postulate
    gel2 : (h : Hom R1 R2) (s' : ♯ S) → Gel R1 s' → Gel R2 s'
    ungel2 : ((s' : ♯ S) → Gel R1 s' → Gel R2 s') → Hom R1 R2
    gel2-ι : (h : Hom R1 R2) (N : S) → gel2 h (ι N) ≡p h .fB N
    {-# REWRITE gel2-ι #-}
    gel2β : (h : Hom R1 R2) → ungel2 (gel2 h) ≡p h
    {-# REWRITE gel2β #-}
    gel2η : (g : (s' : ♯ S) → Gel R1 s' → Gel R2 s') → gel2 (ungel2 g) ≡p g
    {-# REWRITE gel2η #-}

   H2 : (f : ((s' : ♯ S) → Gel R1 s' → Gel R2 s')) (s : S) → ungel2 f .fB s ≡ (λ s' → f (ι s) s')
   H2 f s = sym (eqToPath (gel2-ι (ungel2 f) s))

 module ProductRelation {ℓ ℓ' ℓ'' : Level} (Z : Set ℓ) (Rs : Z → Rel ℓ' ℓ'') where
  open Rel
  prodR : Rel (ℓ ⊔ ℓ') (ℓ ⊔ ℓ'')
  prodR = mkRel ((z : Z) → Rs z .rA) (λ s → (z : Z) → Rs z .rB s) λ v s z → Rs z .rM (v z) s

 module BinProductRelation {ℓ' ℓ'' : Level} (R1 R2 : Rel ℓ' ℓ'') where
  open Rel
  prodR : Rel ℓ' ℓ''
  prodR = mkRel (R1 .rA × R2 .rA) (λ s → R1 .rB s × R2 .rB s) λ v s → (R1 .rM (v .fst) s) , (R2 .rM (v .snd) s)

  module G1 = GelType R1
  module G2 = GelType R2
  module G = GelType prodR
  module GO1 = GelOps (R1 .rA) (R1 .rB) (R1 .rM)
  module GO2 = GelOps (R2 .rA) (R2 .rB) (R2 .rM)
  module GO = GelOps (prodR .rA) (prodR .rB) (prodR .rM)

  fore : (s' : ♯ S) → G1.Gel s' → G2.Gel s' → G.Gel s'
  fore = {!!}

 module GelOpsN {ℓ ℓ' ℓ'' : Level} (Z : Set ℓ) (Rs : Z → Rel ℓ' ℓ'') (R0 : Rel (ℓ ⊔ ℓ') (ℓ ⊔ ℓ'')) where
   open Rel
   open Hom
   open GelType
   open ProductRelation Z Rs

   postulate
    gel2 : (h : Hom prodR R0) (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s'
    ungel2 : ((s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') → Hom prodR R0
    gel2-ι : (h : Hom prodR R0) (N : S) → gel2 h (ι N) ≡p h .fB N
    {-# REWRITE gel2-ι #-}
    gel2β : (h : Hom prodR R0) → ungel2 (gel2 h) ≡p h
    {-# REWRITE gel2β #-}
    gel2η : (g : (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') → gel2 (ungel2 g) ≡p g
    {-# REWRITE gel2η #-}

   H2 : (f : (s' : ♯ S) → ((z : Z) → Gel (Rs z) s') → Gel R0 s') (s : S) → ungel2 f .fB s ≡ (λ s' → f (ι s) s')
   H2 f s = sym (eqToPath (gel2-ι (ungel2 f) s))

data two : Type where
 t0 t1 : two

module RelThmHigher
    (M : (X : Type) → (X → X) → X)
    (Total : Type)
    (Bd : two → Type)
    (proj : Total → (t : two) → Bd t)
    (f : (t : two) → Bd t → Bd t) -- a pair of functions...
    (f~ : (r : Total) → Total) -- ...for which there is evidence that they are related...
    (f~p : (t : two) (r : Total) → proj (f~ r) t ≡ f t (proj r t)) -- ...which really is a relation homomorphism
    where
 -- the theorem I want to prove at this point is there
 -- exists an p' : Total whose boundary is (M (Bd t0) (f t0), M (Bd t1) (f t1))
 open Arity two
 open GelType (mkRel Total Bd proj)
 open GelOps Total Bd proj
 open GelOps2 (mkRel Total Bd proj) (mkRel Total Bd proj)

 p' : Total
 p' = ungel (λ s' → M (Gel s') (gel2 (Arity.mkHom f~ f f~p) s'))

 thm : (t : two) → proj p' t ≡ M (Bd t) (f t)
 thm t = H (λ s' → M (Gel s') (gel2 (Arity.mkHom f~ f f~p) s')) t
