{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality renaming (_≡_ to _≡p_)
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Function.Base

-- Instead of postulating the Gel type, I'm trying to understand it as
-- defined by pushout of copies of the interval

-- This is a version of Gel.agda where
-- I'm trying to make the relations directly indexed by A rather than
-- projecting to A.

module Interval.GelIndexedRel where

abort : ∀ {ℓ} (A : Type ℓ) → ⊥ → A
abort A ()

module main {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

 disc : ∀ {ℓ0} → Set ℓ0 → Set (ℓ ⊔ ℓ0)
 disc A = bridgeDiscrete T A

 module _ {A : {t : T} (e : E t) → Set ℓ} (R : (as : {t : T} (e : E t) → A e) → Set ℓ)
   where

   -- a vector of endpoints to index R by
   AS = {t : T} (e : E t) → A e

   -- total space of R
   R' = Σ AS R

   data Gel (t : T) : Set ℓ where
        gstrand : {as : AS} (r : R as) → Gel t
        gpoint : {e : E t} (a : A e) → Gel t
        gpath : {e : E t} (as : AS) (r : R as) → gpoint (as e) ≡ gstrand r

   ff : {t : T} → (E t) × R' → R'
   ff (e , r) = r

   gg : {t : T} →  (E t) × R' → Σ (E t) A
   gg (e , (as , r)) = (e , as e)

   module gip (t : T) where
     fore : Gel t → Push (ff {t}) gg
     fore (gstrand {as} r) = pinl (as , r)
     fore (gpoint {e} a) = pinr (e , a)
     fore (gpath {e} as r i) = ppath (e , (as , r)) i

     back : Push (ff {t}) gg → Gel t
     back (pinl (as , r)) = (gstrand r)
     back (pinr (e , a)) = (gpoint {e = e} a)
     back (ppath (e , (as , r)) i) = (gpath {e = e} as r i)

     sect : (x : Push (ff {t}) gg) → fore (back x) ≡ x
     sect (pinl a) i = pinl a
     sect (pinr b) i = pinr b
     sect (ppath (c1 , c2) i) j = (ppath (c1 , c2) i)

     retr : (x : Gel t) → back (fore x) ≡ x
     retr (gstrand r) i = gstrand r
     retr (gpoint a) i = gpoint a
     retr (gpath {e} as r i) j = gpath {e = e} as r i

   GelIsPush : (t : T) → Gel t ≅ Push (ff {t}) gg
   GelIsPush t = isoToEquiv (iso fore back sect retr) where
     open gip t

   gel : R' → ((t : T) → Gel t)
   gel (as , r) t = gstrand r

   module _ (Rdisc : disc R')
            (EAdisc : (t : T) → disc (Σ (E t) A))
            (ERdisc : (t : T) → disc ((E t) × R'))
     where

     Commute : isEquiv (pushMap ff gg)
     Commute = ▻Commute (λ _ → Rdisc) EAdisc ERdisc ff gg

     extract-r : Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg) → R'
     extract-r (pinl a) = invIsEq Rdisc a
     extract-r (pinr b) = abort R' (EndNonSurj (fst ∘ b))
     extract-r (ppath c i) = get (get _ ≡ Rdisc .equiv-proof (ff ∘ c) .fst .fst) i where
         get : ∀ {ℓ} (A : Set ℓ) → A
         get A = abort A (EndNonSurj (fst ∘ gg ∘ c))

     invert-r : R' → Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg)
     invert-r r = pinl λ t → r

     retr-r : (g : Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg)) → invert-r (extract-r g) ≡ g
     retr-r (pinl a) i = pinl (secIsEq Rdisc a i)
     retr-r (pinr b) = get (invert-r (get R') ≡ pinr b) where
         get : ∀ {ℓ} (A : Set ℓ) → A
         get A = abort A (EndNonSurj (fst ∘ b))
     retr-r (ppath c i) = get pA i where
         get : ∀ {ℓ} (A : Set ℓ) → A
         get A = abort A (EndNonSurj (λ x → fst (gg (c x))))
         pA = PathP (λ i → invert-r (get (get R' ≡ Rdisc .equiv-proof (ff ∘ c) .fst .fst) i) ≡ ppath c i)
           (λ j → get (invert-r (get R') ≡ pinr (gg ∘ c)) j)
           (λ j → pinl (secIsEq Rdisc (ff ∘ c) j))

     ≅1 : ((t : T) → Gel t) ≅ ((t : T) → Push (ff {t}) gg)
     ≅1 = isoToEquiv (iso (λ g t → gip.fore t (g t)) (λ g t → gip.back t (g t))
                          (λ b i t → gip.sect t (b t) i) (λ a i t → gip.retr t (a t) i))

     ≅2 : ((t : T) → Push (ff {t}) gg) ≅ (Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg))
     ≅2 = isoToEquiv (iso (invIsEq Commute) (funIsEq Commute) (retIsEq Commute) (secIsEq Commute))
     ≅3 : (Push (λ k (t : T) → ff {t} (k t)) (_∘_ gg)) ≅ R'
     ≅3 = isoToEquiv (iso extract-r invert-r (retIsEq Rdisc) retr-r)

     ungel : (g : (t : T) → Gel t) → R'
     ungel g = extract-r (invIsEq Commute (λ t → funIsEq (GelIsPush t .snd) (g t)))

     -- gelβ' : (r : R) → (invIsEq (≅1 .snd) ∘ invIsEq (≅2 .snd) ∘ invIsEq (≅3 .snd)) r ≡ gel r
     -- gelβ' r i = gel r

     -- gelη' : (g : (t : T) → Gel t)  → (funIsEq (≅3 .snd) ∘ funIsEq (≅2 .snd) ∘ funIsEq (≅1 .snd)) g ≡  ungel g
     -- gelη' g i = ungel g

     gelβ : (g : (t : T) → Gel t) → gel (ungel g) ≡ g
     gelβ g  =  cong (invIsEq (≅1 .snd))
               (cong (invIsEq (≅2 .snd))
               (cong (invIsEq (≅3 .snd))
                 (λ i → ungel g)
               ∙ (retIsEq (≅3 .snd)  ((funIsEq (≅2 .snd) ∘ funIsEq (≅1 .snd)) g)))
               ∙ (retIsEq (≅2 .snd)) ((funIsEq (≅1 .snd)) g))
               ∙ (retIsEq (≅1 .snd)) g

     gelη : (r : R') → ungel (gel r) ≡ r
     gelη r = (cong extract-r (retIsEq Commute (pinl (λ t → r)))) ∙ (retIsEq Rdisc r)

     geli : {as : AS} (r : R as) → (t : T) → Gel t
     geli r t = gel (_ , r) t

     endpoint-≅ : {t : T} (e : E t) → Gel t ≅ A e
     endpoint-≅ = {!!}

     endpoint-cvt : {t : T} {e : E t} → Gel t → A e
     endpoint-cvt {t} {e} = funIsEq (endpoint-≅ e .snd)

     ungeli-lemma-side : (g : (t : T) → Gel t) {t : T} (e : E t) → A e
     ungeli-lemma-side g {t} = λ e → {!!}

     -- ungeli-lemma : (g : (t : T) → Gel t) → fst (ungel g) ≡ (λ {t} e → endpoint-cvt (g t))
     -- ungeli-lemma = ?

     ungeli : (g : (t : T) → Gel t) → R (λ {t} e → endpoint-cvt (g t))
     ungeli g = subst R ({!!}) (ungel g .snd) where
       r' : R'
       r' = ungel g