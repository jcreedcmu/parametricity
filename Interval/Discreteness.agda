{-# OPTIONS --cubical --rewriting --allow-unsolved-metas #-}

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

-- ΣPresDisc : ∀ {ℓ0} {A : Set ℓ0} {B : A → Set ℓ0} →
--             bridgeDiscrete A → ((a : A) → bridgeDiscrete (B a)) → bridgeDiscrete (Σ A B)
-- ΣPresDisc {A = A} {B} da db = isoToEquiv (iso fore back sect retr) .snd where
--  back-lemma : (tab : (t : T) → Σ A B) (t : T) → fst (tab t) ≡ invIsEq da (λ x → fst (tab x))
--  back-lemma tab t i = secIsEq da (fst ∘ tab) (~ i) t

--  fore : Σ A B → ((t : T) → Σ A B)
--  fore (a , b) t = (a , b)
--  back : ((t : T) → Σ A B) → Σ A B
--  back tab = invIsEq da (fst ∘ tab) , invIsEq (db (invIsEq da (fst ∘ tab))) λ t → subst B (back-lemma tab t) (tab t .snd)

--  sect : (s : T → Σ A B) → fore (back s) ≡ s
--  sect s i t = back-lemma s t (~ i) , {!!}

--  retr : (s : Σ A B) → back (fore s) ≡ s
--  retr (a , b) i = retIsEq da a i , {!!}


data isConst {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} : (f : A → B) → Set (ℓ ⊔ ℓ') where
 isConst/ : (b : B) → isConst (λ (_ : A) → b)

getit : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} → isConst f → B
getit (isConst/ a) = a

ΣPresAllConst : ∀ {ℓ0} {A : Set ℓ0} {B : A → Set ℓ0}
             → ((fA : T → A) → isConst fA)
             → ((a : A) → (fB : (t : T) → B a) → isConst fB)
             → ((fC : T → Σ A B) → isConst fC)
ΣPresAllConst {A = A} {B} aca acb fC = patternMatch1 (fst ∘ fC) (snd ∘ fC) (aca (fst ∘ fC))  where
   patternMatch2 : (a : A) (fC2 : (t : T) → B a) → isConst fC2 → isConst {B = Σ A B} (λ t → a , fC2 t)
   patternMatch2 a .(λ _ → b) (isConst/ b) = isConst/ (a , b)

   patternMatch1 : (fC1 : T → A) (fC2 : (t : T) → B (fC1 t)) → isConst (fC1) → isConst {B = Σ A B} (λ t → fC1 t , fC2 t)
   patternMatch1 .(λ _ → a) fC2 (isConst/ a) = patternMatch2 a fC2 (acb a fC2)

-- if T is inhabited, then all functions T → A being constant implies A being T-discrete
allConstToDisc : (t : T) → ∀ {ℓ} {A : Set ℓ} → ((f : T → A) → isConst f) → bridgeDiscrete A
allConstToDisc t0 {A = A} fc = isoToEquiv (iso fore back sect retr) .snd where
   fore : A → T → A
   fore a t = a

   back : (T → A) → A
   back f = getit (fc f)

   helper : (f : T → A) → (cc : isConst f) → (t : T) → getit cc ≡ f t
   helper .(λ _ → b) (isConst/ b) t = refl

   sect : (f : T → A) → fore (back f) ≡ f
   sect f i t = helper f (fc f) t i

   retr : (a : A) → getit (fc (λ t → a)) ≡ a
   retr a = helper (λ t → a) (fc (λ t → a)) t0 -- <-- this is the one place we need t0

discToAllConst : ∀ {ℓ} {A : Set ℓ} → bridgeDiscrete A → ((f : T → A) → isConst f)
discToAllConst bd f = subst isConst (secIsEq bd f) (isConst/ (invIsEq bd f))

ΣPresDisc : (t : T) → ∀ {ℓ0} {A : Set ℓ0} {B : A → Set ℓ0} →
            bridgeDiscrete A → ((a : A) → bridgeDiscrete (B a)) → bridgeDiscrete (Σ A B)
ΣPresDisc t0 {A = A} {B} da db = allConstToDisc t0 (ΣPresAllConst (discToAllConst da) λ a → discToAllConst (db a))
