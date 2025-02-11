{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.HITs.Pushout
open import Cubical.Data.Sigma
open import Cubical.HITs.S1

module Graphs where

data Unit {ℓ : Level} : Set ℓ where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

Grph : Set₁
Grph = (E : Set) (∂ : two → E) → Set

Vt : Grph → Set₁
Vt G = (E : Set) (∂ : two → E) → G E ∂

Ed : Grph → Set₁
Ed G = (E : Set) (∂ : two → E) → E → G E ∂

dom : {G : Grph} → Ed G → Vt G
dom {G} e = λ E ∂ → e E ∂ (∂ t0)

cod : {G : Grph} → Ed G → Vt G
cod {G} e = λ E ∂ → e E ∂ (∂ t1)

ref : {G : Grph} → Vt G → Ed G
ref {G} v = λ E ∂ a → v E ∂

refdom : {G : Grph} (v : Vt G) → dom (ref v) ≡ v
refdom v = refl

refcod : {G : Grph} (v : Vt G) → cod (ref v) ≡ v
refcod v = refl

edgeGrph : Grph
edgeGrph E ∂ = E

vertGrph : Grph
vertGrph E ∂ = Unit

module _ (Es : Set) (Vs : Set) (∂s : two → Es → Vs) where
 private module _ (E : Set) (∂ : two → E) where
  pA : Set
  pA = E × Es

  pB : Set
  pB = Vs

  pC : Set
  pC = two × Es

  f : pC → pA
  f (t , e) = (∂ t) , e

  g : pC → pB
  g (t , e) = ∂s t e

  G : Set
  G = Pushout f g

 graph : Grph
 graph = G
