{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

module PushoutTest {ℓ : Level} (T : Set ℓ) where

data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Set ℓ1} {B : Set ℓ2} {C : Set ℓ3}
          (f : C → A) (g : C → B) : Set (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ3)) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  ppath : (c : C) → pinr (g c) ≡ pinl (f c)

pushMap : {k1 k2 k3 : Level}
          {A : Set k1} {B : Set k2} {C : Set k3}
          (f : C → A) (g : C → B)
          (p : Push (λ k (t' : T) → f (k t')) (λ k → g ∘ k)) (t : T) → Push f g
pushMap f g (pinl a) t = pinl (a t)
pushMap f g (pinr b) t = pinr (b t)
pushMap f g (ppath c i) t = ppath (c t) i

tlift : ∀ {ℓ ℓ'} {A : T → Set ℓ} {C : T → Set ℓ'}
        → (f : {t : T} → C t → A t) → ((t : T) → C t) → ((t : T) → A t)
tlift f c t = f (c t)

module depMap {k1 k2 k3 : Level}
          {A : T → Set k1} {B : T → Set k2} {C : T → Set k3}
          (f : {t : T} → C t → A t) (g : {t : T} → C t → B t)
          where

  ff : Σ T C → Σ T A
  ff (t , c) = (t , f c)

  gg : Σ T C → Σ T B
  gg (t , c) = (t , g c)

  outer : Push (tlift (λ {t} → f {t = t})) (tlift g) →
            (t : T) → Push f g
  outer (pinl a) t = pinl (a t)
  outer (pinr b) t = pinr (b t)
  outer (ppath c i) t = ppath (c t) i

  inner : Push (tlift ff) (tlift gg) → T → Push ff gg
  inner = pushMap ff gg


-- The functor T → — commutes with pushouts. The expected map
--   (T → A) +_C (T → B)
--   →
--   T → (A +_C B)
-- is an equivalence.
module _ (T-commute : {k1 k2 k3 : Level}
          {A : Set k1} {B : Set k2} {C : Set k3}
          (f : C → A) (g : C → B)
          → isEquiv (pushMap f g)) where

  module T-dep-commute {k1 k2 k3 : Level}
            {A : T → Set k1} {B : T → Set k2} {C : T → Set k3}
            (f : {t : T} → C t → A t) (g : {t : T} → C t → B t) where

    main : isEquiv (depMap.outer {A = A} f g)
    main = {!pushMap (depMap.ff f g) (depMap.gg f g)!}
