{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (PathP ; sym ; _∙_ ; isContr ; transport ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module toy-problem where

module _ {ℓ : Level} (A R I : Set ℓ) (i0 : I) (f : R → A) where
  data Gel : (i : I) → Set ℓ where
    gel : (r : R) (i : I) → Gel i
    gel0 : (a : A) → Gel i0
    gel0p : (r : R) → gel r i0 ≡c gel0 (f r)

  ind : (C : I → Set ℓ) (g : (r : R) (i : I) → C i)
        (g0 : (a : A) → C i0) (g0p : (r : R) → g r i0 ≡ g0 (f r)) → (i : I) → Gel i → C i
  ind C g g0 g0p i (gel r .i) = g r i
  ind C g g0 g0p i (gel0 a) = g0 a
  ind C g g0 g0p i (gel0p r i₁) = eqToPath (g0p r) i₁

  rec : (P : (i : I) → Gel i → Set ℓ)
       → (g : (r : R) (i : I) → P i (gel r i))
       → (g0 : (a : A) → P i0 (gel0 a))
       → (g0p : (r : R) → PathP (λ i₁ → P i0 (gel0p r i₁)) (g r i0) (g0 (f r))) -- g r i0 ≡ g0 (f r) over P i₀ applied to gel0p r)
       → (i : I) → (x : Gel i) → (P i x)
  rec P g g0 g0p i (gel r .i) = g r i
  rec P g g0 g0p i (gel0 a) = g0 a
  rec P g g0 g0p i (gel0p r i₁) = g0p r i₁

  fore : (i : I) → i ≡ i0 → Gel i → A
  fore i p g = ind (λ _ → A) (λ r _ → f r) (λ x → x) (λ r → refl) i g

  comb : (i : I) → i ≡ i0 → Gel i → A
  comb i p (gel r .i) = f r
  comb i p (gel0 a) = a
  comb i p (gel0p r i₁) = f r

  retract' : (i : I) (a : Gel i) (p : i ≡ i0) → gel0 (fore i p a) ≡c transport (λ t → Gel ((eqToPath p) t)) a
  retract' = {!!}

  retract : (a : Gel i0) → gel0 (fore i0 refl a) ≡c a
  retract a = retract' i0 a refl ∙ Cubical.Foundations.Prelude.transportRefl a
