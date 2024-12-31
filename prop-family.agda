{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (isProp ; isProp→isSet ; isPropIsProp ; PathP ; sym ; _∙_ ; isContr ; transport ; transportRefl ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0 ; i1 to ci1 ; I to cI)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module prop-family where

-- couple of general lemmas
transport-func : ∀ {ℓ k} {I : Set ℓ} {Z : I → Set k} (f : (i : I) → Z i) {i j : I} (p : i ≡c j) →
     transport (λ t → Z (p t)) (f i) ≡c f j
transport-func {Z = Z} f p u = transp (λ t → Z (p (t ∨ u))) u (f (p u))

foo : ∀ {ℓ} (A : Set ℓ) (a b : A) (f : a ≡c b) → PathP (λ i → a ≡c (f i)) (λ _ → a) f
foo A a b f t u = f (t ∧ u)

-- The interval
module _ (I : Set) (E : I → Set) where

  -- assert E i is a proposition. If we take it as a module argument,
  -- rewriting doesn't work.
  postulate
    E-isProp : {i : I} → isProp (E i)

  E-redRefl : {i : I} (x : E i) → E-isProp x x ≡ (λ _ → x)
  E-redRefl {i} x  = pathToEq ((isProp→isSet E-isProp x x) (E-isProp x x) (λ _ → x))
  {-# REWRITE E-redRefl #-}

  module pushout {ℓ : Level} {A : {i : I} (e : E i) → Set ℓ} (R : ({i : I} (e : E i) → A e) → Set ℓ) where

    data Gel : (i : I) → Set ℓ where
      gel : {a : {i : I} (e : E i) → A e} (r : R a) (i : I) → Gel i
      gelι : {i : I} {e : E i} (ae : A e) → Gel i
      gelιp : {i : I} {e : E i} (a : {i : I} (e : E i) → A e) (r : R a) → gelι (a e) ≡c gel r i

    extract : {i : I} {e : E i} → Gel i → A e
    extract {i} {e} (gel {a} r .i) = a e
    extract {i} {e} (gelι {e = e'} ae) = transport (λ t → A (E-isProp e' e t)) ae
--    extract {i} {e} (gelιp {e = e'} a r t) = transport-func a (E-isProp e' e) t
--    expanding def'n of transport-func:
    extract {i} {e} (gelιp {e = e'} a r t) = transp (λ t' → A (E-isProp e' e (t' ∨ t))) t (a (E-isProp e' e t))

    section : {i : I} (e : E i) (ae : A e) → extract (gelι ae) ≡c ae
    section x ax = transportRefl ax

    retract : {i : I} (e : E i) (g : Gel i) → gelι {i} {e} (extract g) ≡c g
    retract e (gel {a} r _) = gelιp a r
    retract {i} e (gelι {e = e'} ae') u = gelι (transp (λ t → A (E-isProp e' e (t ∧ ~ u))) u ae')
    -- Goal: Gel i
    -- ———— Boundary (wanted) —————————————————————————————————————
    -- u = ci0 ⊢ gelι (transport-func a (E-isProp e' e) t)
    -- u = ci1 ⊢ gelιp a r t
    -- t = ci0 ⊢ gelι
    --           (transp (λ t₁ → A (E-isProp e' (E-isProp e e' u) t₁)) u (a e'))
    -- t = ci1 ⊢ gelιp a r u
    -- ————————————————————————————————————————————————————————————
    -- u  : cI
    -- t  : cI
    -- r  : R a
    -- a  : {i = i₁ : I} (e₁ : E i₁) → A e₁
    -- e' : E i
    -- e  : E i
    -- i  : I
    -- R  : ({i = i₁ : I} (e₁ : E i₁) → A e₁) → Set ℓ
    -- A  : {i = i₁ : I} → E i₁ → Set ℓ
    -- ℓ  : Level
    retract {i} e (gelιp {e = e'} a r t) u = {!!}

    Gel-endpoints : {i : I} (e : E i) → Gel i ≅ A e
    Gel-endpoints e = isoToEquiv (Cubical.Foundations.Isomorphism.iso extract gelι (section e) (retract e))
