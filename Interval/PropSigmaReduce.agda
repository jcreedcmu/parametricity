{-# OPTIONS --cubical --rewriting #-}

{- if E is a prop, then
 - Σ E A ≅ Σ E B
 - entails
 - (e : E) → A e ≅ B e
 -}

module Interval.PropSigmaReduce where
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude renaming (_≡_ to _≡c_ ; i0 to ci0 ; i1 to ci1 ; I to cI)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

Σ-contr-eqv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (c : isContr A)
  → (Σ A B) ≅ B (c .fst)
Σ-contr-eqv {A = A} {B} (c@(a0 , cp)) = isoToEquiv (iso fore back section retract) where
  fore : Σ A B → B (a0)
  fore (a , b) = transport (λ t → B (cp a (~ t))) b

  back : B (a0) → Σ A B
  back b = (a0 , b)

  section : (b : B (a0)) → transport (λ t → B (cp a0 (~ t))) b ≡c b
  section b = (λ v → transport (λ t → B (dontCare v (~ t))) b) ∙ transportRefl b where
     dontCare : cp a0 ≡c (λ _ → a0)
     dontCare = isProp→isSet (isContr→isProp c) a0 a0 (cp a0) (λ _ → a0)

  retract : (s : Σ A B) → (a0 , transport (λ t → B (cp (fst s) (~ t))) (snd s)) ≡c s
  retract (a , b) u = (cp a u) , (transp (λ t → B (cp a (~ t ∨ u))) u b)

isProp∙→isContr : ∀ {ℓ} {A : Type ℓ} → isProp A → A → isContr A
isProp∙→isContr prop x .fst = x
isProp∙→isContr prop x .snd y = prop x y

_e⁻¹ : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : Type ℓ₁}
     → (A ≅ B) → (B ≅ A)
_e⁻¹ = invEquiv

_e∙_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
     → A ≅ B → B ≅ C → A ≅ C
_e∙_ = compEquiv

infixr 30 _e∙_
infix 31 _e⁻¹

module _ {ℓ k : Level} {E : Set ℓ} {A : E → Set k} {B : Set k}
        (f : (e : E) → A e → B) where
  packFunc : Σ E A → B
  packFunc (e , a) = f e a

module _ {ℓ k : Level} (E : Set ℓ) (A : E → Set k) (B : Set k) (E-isProp : isProp E)
        (f : (e : E) → A e → B) (fEq : isEquiv (packFunc f)) where

  thm : (e : E) → isEquiv (f e)
  thm e =  ((Σ-contr-eqv (isProp∙→isContr E-isProp e) e⁻¹) e∙ (packFunc f , fEq)) .snd
