{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary

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

module _ {ℓ1 ℓ2 : Level} {D : Set ℓ1} {S : Set ℓ2} where
  private
    ℓ = ℓ-max ℓ1 ℓ2
    T = D ▻ S

  pushMap : {k1 k2 k3 : Level}
            {A : Type k1} {B : Type k2} {C : Type k3}
            (f : C → T → A) (g : C → T → B)
            (p : Push f g) (d : T) → Push (λ c → f c d) (λ c → g c d)
  pushMap f g (pinl a) d = pinl (a d)
  pushMap f g (pinr b) d = pinr (b d)
  pushMap f g (ppath c i) d = ppath c i

  postulate
    -- The endpoints of the interval...
    end : S → T

    -- ...constitute an embedding...
    endIsEmbed : isEmbedding end

    -- ...which is not an equivalence
    endNonTriv : ¬ (isEquiv end)

    -- The type D is discrete with respect to the interval T.
    -- the only maps T → D are the constant maps.
    ▻Discrete : isEquiv (λ (d : D) (t : T) → d)

    -- The functor T → — commutes with pushouts. The expected map
    --   (T → A) +_C (T → B)
    --   →
    --   T → (A +_C B)
    -- is an equivalence.
    ▻Commute : {k1 k2 k3 : Level}
            {A : Type k1} {B : Type k2} {C : Type k3}
            (f : C → T → A) (g : C → T → B)
            → isEquiv (pushMap f g)

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
