{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv ; equivFun)
open import Agda.Primitive using (Level ; _⊔_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
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
  End t = Σ[ s ∈ S ] end s ≡ t

  -- It is a mere proposition
  EndIsProp : (i : D ▻ S) → isProp (End i)
  EndIsProp t (s1 , p1) (s2 , p2) i = invIsEq (endIsEmbed s1 s2) (p1 ∙ sym p2) i , {!!}

   -- Not all points are endpoints
  EndNonTriv : ((i : D ▻ S) → End i) → ⊥
  EndNonTriv = {!!}

  -- The endpoints are isomorphic to S
  EndIsS : Σ (D ▻ S) End ≅ S
  EndIsS = isoToEquiv (iso fore back sect retr) where
    fore : Σ (D ▻ S) End → S
    fore (t , s , p) = s

    back : S → Σ (D ▻ S) End
    back s = (end s) , (s , (λ _ → end s))

    sect : (s : S) → fore (back s) ≡ s
    sect s _ = s

    retr : (x : Σ (D ▻ S) End) → back (fore x) ≡ x
    retr (t , s , p) i = (p i) , (s , (λ j → p (i ∧ j)))
