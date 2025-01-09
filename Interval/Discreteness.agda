{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (_⊎_ to _+_)
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

module Interval.Discreteness  where

module _ {ℓ : Level} (T : Set ℓ) where
 -- bridgeDiscrete A := A has no T-cohesion
 bridgeDiscrete : ∀ {ℓ0} (A : Set ℓ0) → Set (ℓ ⊔ ℓ0)
 bridgeDiscrete A = isEquiv (λ (a : A) (t : T) → a)

 -- discreteness is preserved by Σ
 ΣPresDisc : ∀ {ℓ0} {ℓ1} {A : Set ℓ0} {B : A → Set ℓ1} →
             bridgeDiscrete A → ((a : A) → bridgeDiscrete (B a)) → bridgeDiscrete (Σ A B)
 ΣPresDisc {A = A} {B} da db = compEquiv step1 (compEquiv step2 step3) .snd where
     step1 : Σ A (λ a →  B a) ≅ Σ A (λ a → T → B a)
     step1 = Σ-cong-equiv-snd (λ a → funIsEq (db a) , db a)

     step2 : Σ A (λ a → T → B a) ≅ Σ (T → A) (λ f → (t : T) → B (f t))
     step2 = Σ-cong-equiv-fst (funIsEq da , da)

     step3 : Σ (T → A) (λ f → (t : T) → B (f t)) ≅ (T → Σ A B)
     step3 = isoToEquiv (iso fore back sect retr) where
       fore : Σ (T → A) (λ f → (t : T) → B (f t)) → (T → Σ A B)
       fore (ta , tb) t = (ta t) , (tb t)

       back : (T → Σ A B) → Σ (T → A) (λ f → (t : T) → B (f t))
       back tab = (λ t → tab t .fst) , (λ t → tab t .snd)

       sect : (tab : T → Σ A B) → fore (back tab) ≡ tab
       sect tab i t = (tab t .fst) , (tab t .snd)

       retr : (tab : Σ (T → A) (λ f → (t : T) → B (f t))) → back (fore tab) ≡ tab
       retr tab i = tab .fst , tab .snd

 -- discreteness is preserved by product
 prodPresDisc : ∀ {ℓ0} {ℓ1} {A : Set ℓ0} {B : Set ℓ1} → bridgeDiscrete A → bridgeDiscrete B → bridgeDiscrete (A × B)
 prodPresDisc {A = A} {B} da db = ΣPresDisc da (λ _ → db)

 propIsDisc : ∀ {ℓ} {A : Set ℓ} (isPropA : isProp A) (t : T) → bridgeDiscrete A
 propIsDisc {A = A} isPropA t0 = isoToEquiv (iso fore back sect retr) .snd where
  fore : A → T → A
  fore a t = a

  back : (T → A) → A
  back f = f t0

  sect : (f : T → A) → fore (back f) ≡ f
  sect f i t = isPropA (f t0) (f t) i

  retr : (a : A) → back (fore a) ≡ a
  retr a i = a
