{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Unit
open import Cubical.Data.Sum renaming (_⊎_ to _+_)
open import Cubical.Data.Empty
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

module PushoutTest2 where

record Graph : Set₁ where
 field
  V : Set
  E : V → V → Set
  rf : (v : V) → E v v
open Graph

record Hom (G1 G2 : Graph) : Set where
 field
  Vmap : G1 .V → G2 .V
  Emap : {v1 v2 : G1 .V} → G1 .E v1 v2 → G2 .E (Vmap v1) (Vmap v2)
  rf-pres : (v : G1 .V) → Emap (G1 .rf v) ≡ G2 .rf (Vmap v)
open Hom

data Two : Set where
 t0 t1 : Two

step : Graph
step = record { V = Two ; E = StepEdge ; rf = {!StepRf!} } where
  StepEdge : Two → Two → Set
  StepEdge t0 t0 = Unit
  StepEdge t0 t1 = Unit
  StepEdge t1 t0 = ⊥
  StepEdge t1 t1 = Unit

  StepRf : (v : Two) → StepEdge v v
  StepRf t0 = tt
  StepRf t1 = tt

totalRf : (G : Graph) → G .V → Σ[ v1 ∈ G .V ] Σ[ v2 ∈ G .V ] G .E v1 v2
totalRf G v = v , v , G .rf v

disc1 : Graph → Set
disc1 G = isEquiv (totalRf G)

mkdisc : Set → Graph
mkdisc X = record { V = X ; E = _≡_ ; rf = λ x → refl }

mkfdisc : (A B : Set) (R : A → B → Set) → Graph
mkfdisc A B R = record { V = lV ; E = lE ; rf = lrf } where
   lV = A + B
   lE : lV → lV → Set
   lE (inl x) (inl y) = x ≡ y
   lE (inl x) (inr y) = R x y
   lE (inr x) (inl y) = ⊥
   lE (inr x) (inr y) = x ≡ y
   lrf : (v : lV) → lE v v
   lrf (inl x) = refl
   lrf (inr x) = refl


data Push {ℓ1 ℓ2 ℓ3 : Level}
          {A : Set ℓ1} {B : Set ℓ2} {C : Set ℓ3}
          (f : C → A) (g : C → B) : Set (ℓ-max ℓ1 (ℓ-max ℓ2 ℓ3)) where
  pinl : (a : A) → Push f g
  pinr : (b : B) → Push f g
  ppath : (c : C) → pinr (g c) ≡ pinl (f c)

Gpush : {A : Graph} {B : Graph} {C : Graph}
        (f : Hom C A) (g : Hom C B) → Graph
Gpush {A} {B} {C} f g = record { V = {!!} ; E = {!!} ; rf = {!!} } where
   lV = Push (f .Vmap) (g .Vmap)
   lE : lV → lV → Set
   lE (pinl a) (pinl a₁) = {!!}
   lE (pinl a) (pinr b) = {!!}
   lE (pinl a) (ppath c i) = {!!}
   lE (pinr b) x₁ = {!!}
   lE (ppath c i) x₁ = {!!}
-- I want to understand what the pushout of three relations looks like

module _ (A A' B B' C C' : Set)
  (f : C → A) (f' : C' → A')
  (g : C → B) (g' : C' → B')
  (RA : A → A' → Set)
  (RB : B → B' → Set)
  (RC : C → C' → Set)  where

  P : Set
  P = Push f g

  P' = Push f' g'
