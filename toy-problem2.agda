{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (PathP ; sym ; _∙_ ; isContr ; transport ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0)
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

module _ {ℓ : Level} (A R I : Set ℓ) (i0 : I) (f : R → A) where
  data Gel : (i : I) → Set ℓ where
    gel : (r : R) (i : I) → Gel i
    gel0 : (a : A) → Gel i0
    gel0p : (r : R) → gel r i0 ≡c gel0 (f r)

  get-a : (i : I) (p : i ≡c i0) → Gel i → A
  get-a i p (gel r .i) = {!!}
  get-a i p (gel0 a) = {!!}
  get-a i p (gel0p r i₁) = {!!}
