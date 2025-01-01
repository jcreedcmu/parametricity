{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv ; equivFun)
open import Agda.Primitive using (Level ; _⊔_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base using (¬_)
open import Function.Base

module IntervalAxioms where

data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Type ℓ1} {B : Type ℓ2} {C : Type ℓ3}
          (f : C → A) (g : C → B) : Set (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ3)) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  pe : (c : C) → pinl (f c) ≡ pinr (g c)

postulate
  -- D ▻ S is an interval type of "direction" D and "shape S"
  _▻_ : {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) → Set (ℓ-max ℓ1 ℓ2)


module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
  private
    ℓ = ℓ-max ℓ1 ℓ2

  pushMap : {k1 k2 k3 : Level}
            {A : Type k1} {B : Type k2} {C : Type k3}
            (f : C → D ▻ S → A) (g : C → D ▻ S → B)
            (p : Push {A = D ▻ S → A} f g) (d : D ▻ S) → Push (λ c → f c d) (λ c → g c d)
  pushMap f g (pinl a) d = pinl (a d)
  pushMap f g (pinr b) d = pinr (b d)
  pushMap f g (pe c i) d = pe c i

  postulate
    -- The endpoints of the interval
    end : S → D ▻ S

    -- ...constitute an embedding
    endIsEmbed : isEmbedding end

    -- ...which is not an equivalence
    endNonTriv : isEquiv end → ⊥

    -- The type D is discrete with respect to the interval D ▻ S
    ▻Discrete : isEquiv (λ (d : D) (t : D ▻ S) → d)

    -- The functor D ▻ S → — commutes with pushouts,
    -- D ▻ S → (A +_C B) ≅ (D ▻ S → A) +_C (D ▻ S → B)
    ▻Commute : {k1 k2 k3 : Level}
            {A : Type k1} {B : Type k2} {C : Type k3}
            (f : C → D ▻ S → A) (g : C → D ▻ S → B)
            (p : Push {A = D ▻ S → A} f g) (d : D ▻ S) → Push (λ c → f c d) (λ c → g c d)
            → isEquiv (pushMap f g)

  -- The endpoint predicate on the interval
  End : D ▻ S → Set ℓ
  End = fiber end

  -- It is a mere proposition
  EndIsProp : (t : D ▻ S) → isProp (End t)
  EndIsProp t = isEmbedding→hasPropFibers endIsEmbed t

   -- Not all points are endpoints
  EndNonTriv : ((t : D ▻ S) → End t) → ⊥
  EndNonTriv surj = endNonTriv ( record { equiv-proof = fiberIsContr }) where
    fiberIsContr : (t : D ▻ S) → isContr (fiber end t)
    fiberIsContr t = surj t , EndIsProp t (surj t)

  -- The endpoints are isomorphic to S
  EndIsS : Σ (D ▻ S) End ≅ S
  EndIsS = isoToEquiv (iso
    (λ {(t , s , p) → s})
    (λ s → end s , s , (λ _ → end s))
    (λ s _ → s)
    (λ {(t , s , p) i → (p i) , (s , (λ j → p (i ∧ j)))}))
