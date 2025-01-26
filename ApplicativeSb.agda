{-# OPTIONS --cubical --rewriting --type-in-type #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base
open import Applicative

module ApplicativeSb where


module _ {D : Dapp} where
 open Dapp D
 open Dapp (dbar D) using () renaming (F to Fbar ; η to ηbar ; Fd to Fdbar ; _·_ to _·bar_ ; d⟪_,_⟫ to d⟪_,_⟫bar)
 open Substs D
 open Substs (dbar D) using () renaming (F/ to F/bar)
 open Extend (dbar D)
 open Star D
 open SubstCoerce D
 open Applicative.Main D

 -- FIXME: Broken universe check here, not sure I understand why yet
 postulate
  piRule : ∀ {ℓ ℓ'} {t : Tele ℓ'} (ϕ : Fbar ⟦ t ⟧) (A : ⟦ t ⟧ → Type ℓ) (B : (g : ⟦ t ⟧) → A g → Type ℓ)
          (f : F/ (∂ ϕ) (λ g → (a : A g) → B g a)) →
          fib/ ϕ (λ g → (a : A g) → B g a) f ≡ ((a : F/bar ϕ A) → fib/ (extend ϕ a) (λ g → B (g .fst) (g .snd)) ((star (∂ ϕ) A B f (∂/ ϕ a))))


pthm : (id : (X : Type) → X → X) (A B : Type) (R : A × B → Type) (a : A) (b : B) (r : R (a , b)) → R (id A a , id B b)
pthm id A B R a b r = {!fibIn/ (ηbar id)!} where
 open Dapp binary
 open Dapp (dbar binary) using () renaming (F to Fbar ; η to ηbar)

module _ where
 open Dapp binary
 open Dapp (dbar binary) using () renaming (F to Fbar ; η to ηbar)
 open SubstCoerce binary
 open Substs binary
 open Substs (dbar binary) using () renaming (F/ to F/bar)
 open Extend binary
 open Extend (dbar binary) using () renaming (extend to extendbar)
 open Star binary
 open Applicative.Main binary

 pthm2Res : (a₁ : F/bar (ηbar ⋆) (λ _ → Type)) (id : (X : Type) → X → X) → Type₁
 pthm2Res a₁ id = fib/ (extendbar (ηbar ⋆) a₁) (λ g → g .snd → g .snd) {!foo!} where
   foo : Substs.F/ binary
      (extend (⋆ , ⋆) (∂/ (ηbar ⋆) a₁))
      (λ g → g .snd → g .snd)
   foo = star (∂ (ηbar ⋆)) (λ _ → Type) (λ _ X → X → X) (into/ (id , id)) (∂/ (ηbar ⋆) a₁)

 pthm2 : (id : (X : Type) → X → X) (A B : Type) (R : A × B → Type) (a : A) (b : B) (r : R (a , b)) →
     (a₁ : F/bar (ηbar ⋆) (λ _ → Type)) → pthm2Res a₁ id
      -- (a₁ : Substs.F/ (dbar binary) (ηbar ⋆) (λ _ → Type)) →
      -- fib/ (Extend.extend (dbar binary) (ηbar ⋆) a₁)
      -- (λ g → g .snd → g .snd)
      -- (star (∂ (ηbar ⋆)) (λ _ → Type) (λ _ X → X → X)
      --  (SubstCoerce.into/ binary (id , id)) (∂/ (ηbar ⋆) a₁))
--   ((a : F/bar (ηbar ⋆) (λ _ → Type)) → fib/ (extend (ηbar ⋆) a) (λ g → (g .snd) → (g .snd)) (star (∂ (ηbar ⋆)) ? (∂/ (ηbar ⋆) a)))
-- fib/ (ηbar ⋆) (λ _ → (X : Type) → X → X) (into/ (id , id))


 pthm2 id A B R a b r = {!transport (piRule (ηbar ⋆) (λ _ → Type) (λ _ X → (X → X)) (into/ (η id))) (fibIn/ (ηbar id))!}
-- fib/ (ηbar ⋆) (λ _ → (X : Type) → X → X) (into/ (id , id))
--
