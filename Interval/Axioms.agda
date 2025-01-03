{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

module Interval.Axioms where

data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B) : Set (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ3)) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  ppath : (c : C) → pinr (g c) ≡ pinl (f c)

postulate
  -- D ▻ S is an interval type of "direction" D and "shape S"
  _▻_ : {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) → Set (ℓ-max ℓ1 ℓ2)

-- bridgeDiscrete A := A has no T-cohesion
bridgeDiscrete : ∀ {ℓ0 ℓ1} (T : Set ℓ1) (A : Set ℓ0)→ Set (ℓ1 ⊔ ℓ0)
bridgeDiscrete T A = isEquiv (λ (a : A) (t : T) → a)

module _ {ℓ1 ℓ2 : Level} {D : Set ℓ1} {S : Set ℓ2} where
  private
    ℓ = ℓ-max ℓ1 ℓ2
    T = D ▻ S

  pushMap : {k1 k2 k3 : Level}
            {A : T → Type k1} {B : T → Type k2} {C : T → Type k3}
            (f : {t : T} → C t → A t) (g : {t : T} → C t → B t)
            (p : Push (λ k (t' : T) → f (k t')) (λ k → g ∘ k)) (t : T) → Push (f {t}) (g {t})
  pushMap f g (pinl a) t = pinl (a t)
  pushMap f g (pinr b) t = pinr (b t)
  pushMap f g (ppath c i) t = ppath (c t) i


  postulate
    -- The endpoints of the interval...
    end : S → T

    -- ...constitute an embedding...
    endIsEmbed : isEmbedding end

    -- ...which is not an equivalence
    endNonTriv : ¬ (isEquiv end)

    -- The type D is discrete with respect to the interval T.
    -- the only maps T → D are the constant maps.
    ▻Discrete : bridgeDiscrete T D

    -- The functor T → — commutes with T-dependent pushouts, when all of the
    -- fibers are path-discrete. The expected map
    --   ((t : T) → A t) +_((t:T) → C t) ((t : T) → B t)
    --   →
    --   (t : T) → (A t +_(C t) B t)
    -- is an equivalence.
    ▻Commute : {k1 k2 k3 : Level}
            {A : T → Type k1} {B : T → Type k2} {C : T → Type k3}
            (Adisc : (t : T) → bridgeDiscrete T (A t))
            (Bdisc : (t : T) → bridgeDiscrete T (B t))
            (Cdisc : (t : T) → bridgeDiscrete T (C t))
            (f : {t : T} → C t → A t) (g : {t : T} → C t → B t)
            → isEquiv (pushMap {A = A} f g)

  -- For convenience, phrase these axioms equivalently in terms of an
  -- endpoint predicate on the interval.

  -- The predicate
  End : T → Set ℓ
  End = fiber end

  -- It is a mere proposition
  EndIsProp : (t : T) → isProp (End t)
  EndIsProp t = isEmbedding→hasPropFibers endIsEmbed t

   -- Not all points are endpoints
  EndNonTriv : ¬ ((t : T) → End t)
  EndNonTriv surj = endNonTriv ( record { equiv-proof = fiberIsContr }) where
    fiberIsContr : (t : T) → isContr (fiber end t)
    fiberIsContr t = surj t , EndIsProp t (surj t)

  -- The endpoints are isomorphic to S
  EndIsS : Σ T End ≅ S
  EndIsS = isoToEquiv (iso
    (λ {(t , s , p) → s})
    (λ s → end s , s , (λ _ → end s))
    (λ s _ → s)
    (λ {(t , s , p) i → (p i) , (s , (λ j → p (i ∧ j)))}))

  EndNonSurj : ¬ ((t : T) → fiber end t)
  EndNonSurj surj = endNonTriv (isEmbedding×isSurjection→isEquiv (endIsEmbed , λ t → ∣ surj t ∣₁))
