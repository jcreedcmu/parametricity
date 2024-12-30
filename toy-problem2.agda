{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (PathP ; sym ; _∙_ ; isContr ; transport ; transportRefl ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module toy-problem2 where

module easy {ℓ : Level} (A B : Set ℓ) (b0 : B) where
  data Push : B → Set ℓ where
    strand : (a : A) (b : B) → Push b
    point : (a : A) → Push b0
    eq : (a : A) → strand a b0 ≡c point a

  get-a : {b : B} (p : b ≡c b0) → Push b → A
  get-a p (strand a b) = a
  get-a p (point a) = a
  get-a p (eq a i) = a

  section : (a : A) → get-a (λ _ → b0) (strand a b0) ≡c a
  section a _ = a

  retract' : (b : B) (p : b ≡c b0) (x : Push b) → strand (get-a p x) b ≡c x
  retract' b p (strand a .b) t = strand a b
  retract' b p (point a) = eq a
  retract' b p (eq a i) = λ j → eq a (i ∧ j)

  retract : (x : Push b0) → strand (get-a (λ _ → b0) x) b0 ≡c x
  retract x = retract' b0 (λ _ → b0) x

  Push0≅A : Push b0 ≅ A
  Push0≅A = isoToEquiv (Cubical.Foundations.Isomorphism.iso (get-a (λ _ → b0)) (λ a → strand a b0) section retract)

module med where
  data S1 : Set where
     base : S1
     loop : base ≡c base

  data Fig : S1 → Set where
     top bot : (s : S1) → Fig s
     join : top base ≡c bot base
  -- extra : Fig base
  -- join1 : top base ≡c extra
  -- join2 : bot base ≡c extra

  data unit : Set where
     * : unit


  thm' : (s : S1) (f : Fig s) (p : base ≡c s ) → top s ≡c f
  thm' s (top .s) p = λ t → top s
  thm' s (bot .s) p = transport (λ t → top (p t) ≡c bot (p t)) join
  thm' .base (join i) p = {!!}

  thm : (f : Fig base) → top base ≡c f
  thm f = thm' base f (λ _ → {!!})

module hard {ℓ : Level} (A B C : Set ℓ) (f : A → C) (b0 : B) where
  data Push : B → Set ℓ where
    strand : (a : A) (b : B) → Push b
    point : (c : C) → Push b0
    eq : (a : A) → strand a b0 ≡c point (f a)

  get-c : {b : B} (p : b ≡c b0) → Push b → C
  get-c p (strand a b) = f a
  get-c p (point a) = a
  get-c p (eq a i) = f a

  section : (c : C) → c ≡c c
  section c i = c

  pointat : {b : B} (p : b ≡c b0) (c : C) → Push b
  pointat p x = transport (λ t → Push (p (~ t))) (point x)

  retract' : (b : B) (p : b ≡c b0) (x : Push b) → pointat p (get-c p x) ≡c x
  retract' b p (strand a .b) = {!!}
  retract' b p (point c) = {!!}
  retract' b p (eq a i) = {!!}

  retract : (a : Push b0) → point (get-c (λ _ → b0) a) ≡c a
  retract x = sym (transportRefl (point (get-c (λ _ → b0) x))) ∙ retract' b0 (λ _ → b0) x --

  Push0≅A : Push b0 ≅ C
  Push0≅A = isoToEquiv (Cubical.Foundations.Isomorphism.iso (get-c (λ _ → b0)) point section retract)
