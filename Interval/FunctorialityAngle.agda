{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
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
import Interval.Gel

{-
 - I'm still trying to find a good approach to Functoriality that doesn't
 - entangle everything together simultaneously. The idea here is
 - to suppose that there is some type Gel t that *happens* to be
 - isomorphic to the pushout of
 - gstrand : ((t' : T) → Gel t') → Gel t
 - gpoint : (e : E t)  → Gel t
 -}
module Interval.FunctorialityAngle where

postulate
 T : Set
 E Gel H : T → Set

data View  (t : T) : Set where
 vstrand : (g : (t' : T) → Gel t') → View t
 vpoint : (e : E t) → Gel t → View t
 vpath : (e : E t) (g : (t' : T) → Gel t') → vstrand {t} g ≡ vpoint e (g t)

View2Gel : (t : T) → View t → Gel t
View2Gel t (vstrand g) = g t
View2Gel t (vpoint e x) = x
View2Gel t (vpath e g i) = g t

postulate
 -- eq : (t : T) → Gel t ≅ View t
 visEq : (t : T) → isEquiv (View2Gel t)
 ah : (t : T) (e : E t) → Gel t → H t

Γ : (T → Set) → Set
Γ H = (t : T) → H t



fore : ( (Σ[ f ∈ ((t : T) → Gel t → H t) ] ((t : T)(e : E t) → f t ≡ ah t e)))
        → (Σ[ f ∈ (Γ Gel → Γ H) ] ((t : T) (e : E t) (g : Γ Gel) → f g t ≡ ah t e (g t)))

fore (f , f') = (λ g t → f t (g t)) , λ t e g i → f' t e i (g t)

processView : (f  : Γ Gel → Γ H) (f' : (t : T) (e : E t) (g : Γ Gel) → f g t ≡ ah t e (g t))
              (t : T) (v : View t) → H t
processView f f' t (vstrand g) = f g t
processView f f' t (vpoint e g) = ah t e g
processView f f' t (vpath e g i) = f' t e g i

processView' : (f  : Γ Gel → Γ H) (f' : (t : T) (e : E t) (g : Γ Gel) → f g t ≡ ah t e (g t))
              (t : T) (e : E t) (g : Gel t) → processView f f' t (invIsEq (visEq t) g) ≡ ah t e g
processView' f f' t e g i with invIsEq (visEq t) g
processView' f f' t e g i | vstrand g' = {!f' t e g' i!}
processView' f f' t e g i | vpoint e' g' = {!!}
processView' f f' t e g i | vpath e' g' j = {!!}

back : (Σ[ f ∈ (Γ Gel → Γ H) ] ((t : T) (e : E t) (g : Γ Gel) → f g t ≡ ah t e (g t)))
       → ( (Σ[ f ∈ ((t : T) → Gel t → H t) ] ((t : T)(e : E t) → f t ≡ ah t e)))
back (f , f') = (λ t g → processView f f' t (invIsEq (visEq t) g)) , λ t e i g → processView' f f' t e g i
