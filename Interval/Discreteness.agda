{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

module Interval.Discreteness {ℓ : Level} (T : Set ℓ) where

-- bridgeDiscrete A := A has no T-cohesion
bridgeDiscrete : ∀ {ℓ0} (A : Set ℓ0) → Set (ℓ ⊔ ℓ0)
bridgeDiscrete A = isEquiv (λ (a : A) (t : T) → a)

prodLem : ∀ {ℓ0} {A B : Set ℓ0} {ab ab' : A × B}
  (p1 : proj₁ ab ≡ proj₁ ab') (p2 : proj₂ ab ≡ proj₂ ab') → ab ≡ ab'
prodLem {ab = ab} {ab'} p1 p2 = ×-η ab ∙ (λ i → (p1 i , p2 i)) ∙ sym (×-η ab')

prodPresDisc : ∀ {ℓ0} {A B : Set ℓ0} → bridgeDiscrete A → bridgeDiscrete B → bridgeDiscrete (A × B)
prodPresDisc {A = A} {B} da db = isoToEquiv (iso fore back sect retr) .snd where
  fore : A × B → ((t : T) → A × B)
  fore ab t = ab

  back : ((t : T) → A × B) → A × B
  back tab = (invIsEq da (proj₁ ∘ tab)) , (invIsEq db (proj₂ ∘ tab))

  sect : (tab : (t : T) → A × B) → fore (back (tab)) ≡ tab
  sect tab i t = prodLem {ab = fore (back (tab)) t} {ab' = tab t}
         (λ i → secIsEq da (λ t → proj₁ (tab t)) i t)
         (λ i → secIsEq db (λ t → proj₂ (tab t)) i t) i

  retr : (ab : A × B) → back (fore ab) ≡ ab
  retr (a , b) i = retIsEq da a i , retIsEq db b i

ΣPresDisc : ∀ {ℓ0} {A : Set ℓ0} {B : A → Set ℓ0} →
            bridgeDiscrete A → ((a : A) → bridgeDiscrete (B a)) → bridgeDiscrete (Σ A B)
ΣPresDisc {A = A} {B} da db = isoToEquiv (iso fore back sect retr) .snd where
 back-lemma : (tab : (t : T) → Σ A B) (t : T) → fst (tab t) ≡ invIsEq da (λ x → fst (tab x))
 back-lemma tab t i = secIsEq da (fst ∘ tab) (~ i) t

 fore : Σ A B → ((t : T) → Σ A B)
 fore (a , b) t = (a , b)
 back : ((t : T) → Σ A B) → Σ A B
 back tab = invIsEq da (fst ∘ tab) , invIsEq (db (invIsEq da (fst ∘ tab))) λ t → subst B (back-lemma tab t) (tab t .snd)

 sect = {!!}
 retr = {!!}
