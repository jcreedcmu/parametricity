{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

module PushoutTest {ℓ : Level} (T : Set ℓ) where

_isEq∙_ : ∀ {ℓ} {A B C : Set ℓ} {f : B → C} {g : A → B} →
          isEquiv f → isEquiv g → isEquiv (f ∘ g)
fe isEq∙ ge = {!!} -- surely this should be in a library somewhere
infixr 30 _isEq∙_

Π : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Π A B = (x : A) → B x

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

  outer : Push {A = Π T A} (tlift f) (tlift g) →
          (t : T) → Push {A = A t} f g
  outer (pinl a) t = pinl (a t)
  outer (pinr b) t = pinr (b t)
  outer (ppath c i) t = ppath (c t) i

  prefix-get : (Push {A = T → Σ T A} (tlift ff) (tlift gg)) → T → T
  prefix-get (pinl a) = fst ∘ a
  prefix-get (pinr b) = fst ∘ b
  prefix-get (ppath c i) = fst ∘ c

  prefix : Push {A = Π T A} (tlift f) (tlift g) →
           Σ (Push {A = T → Σ T A} (tlift ff) (tlift gg)) (λ g → (t : T) → prefix-get g t ≡ t)
  prefix (pinl a) = (pinl (λ t → t , a t)) , λ t → refl
  prefix (pinr b) = (pinr (λ t → t , b t)) , λ t → refl
  prefix (ppath c i) = (ppath (λ t → t , c t) i) , λ t → refl

  prefixIsEquiv : isEquiv prefix
  prefixIsEquiv = {!!}

  suffix-get : Push {A = Σ T A} ff gg → T
  suffix-get (pinl a) = fst a
  suffix-get (pinr b) = fst b
  suffix-get (ppath c i) = fst c

  suffix-lemma : (x : Push {A = Σ T A} ff gg) → Push {A = A (suffix-get x)} f g
  suffix-lemma (pinl a) = pinl (a .snd)
  suffix-lemma (pinr b) = pinr (b .snd)
  suffix-lemma (ppath c i) = ppath (c .snd) i

  suffix : (Σ[ g ∈ (T → Push {A = Σ T A} ff gg) ] ((t : T) → suffix-get (g t) ≡ t)) →
            (t : T) → Push {A = A t} f g
  suffix (x , good) t  = subst (λ z → Push {A = A z} f g) (good t) (suffix-lemma (x t))

  suffixIsEquiv : isEquiv suffix
  suffixIsEquiv = {!!}

  med : (Σ (Push {A = T → Σ T A} (tlift ff) (tlift gg)) (λ g → (t : T) → prefix-get g t ≡ t)) →
        (Σ[ g ∈ (T → Push {A = Σ T A} ff gg) ] ((t : T) → suffix-get (g t) ≡ t))
  med (pinl a , good) = pinl ∘ a , good
  med (pinr b , good) = pinr ∘ b , good
  med (ppath c i , good) = (λ t → ppath (c t) i) , good

  areSame : suffix ∘ med ∘ prefix ≡ outer
  areSame = {!!}
  -- areSame i (pinl a) t = {!!}
  -- areSame i (pinr b) t = {!!}
  -- areSame i (ppath c j) t = {!!}


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

    -- this is where I should use T-commute
    medIsEquiv : isEquiv (depMap.med (λ {t} → f {t}) g)
    medIsEquiv = {!!}

    main : isEquiv (depMap.outer {A = A} f g)
    main = subst isEquiv (depMap.areSame f g) composed where
       composed : isEquiv (depMap.suffix (λ {t} → f {t}) g ∘ depMap.med f g ∘ depMap.prefix f g)
       composed = (depMap.suffixIsEquiv f g) isEq∙ medIsEquiv isEq∙ (depMap.prefixIsEquiv f g)
