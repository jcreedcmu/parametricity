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
 R : Set

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
 ah : (t : T) (e : E t) → View t → H t

Γ : (T → Set) → Set
Γ H = (t : T) → H t

g2v : {t : T} → Gel t → View t
g2v {t} g = invIsEq (visEq t) g

gg2vv : Γ Gel → Γ View
gg2vv gg = g2v ∘ gg

record PushRec1 (t : T) : Set where
 constructor pushRec1
 field
  pr1f : (t : T) → View t → H t
  pr1a : (t : T)(e : E t) → pr1f t ≡ ah t e

record PushRec2 (t : T) : Set where
 constructor pushRec2
 field
  pr2strand : (gg : Γ Gel) → H t
  pr2point : (e : E t) (g : Gel t) → H t
  pr2path : (e : E t) (gg : Γ Gel) → pr2strand gg ≡ pr2point e (gg t)

dissect : (t : T) (pr2 : PushRec2 t) (v : View t) → H t
dissect t pr2 (vstrand g) = pr2 .PushRec2.pr2strand g
dissect t pr2 (vpoint e₁ x) = pr2 .PushRec2.pr2point e₁ x
dissect t pr2 (vpath e₁ g i) = pr2 .PushRec2.pr2path e₁ g i

record PushRec3 (t : T) : Set where
 constructor pushRec3
 field
  pr3pr2 : PushRec2 t
  pr3a : (e : E t) → dissect t pr3pr2 ≡ ah t e

module ≅1 where
  fore : ((t : T) → View t → H t) → Γ PushRec2
  fore f t = pushRec2 (λ gg → f t (vstrand gg)) (λ e g → f t (vpoint e g)) λ e gg i → f t (vpath e gg i)

  back : Γ PushRec2 → ((t : T) → View t → H t)
  back pp t v = dissect t (pp t) v

  sect : (pp : Γ PushRec2) → fore (back pp) ≡ pp
  sect pp i = pp

  retr : (f : (t : T) → View t → H t) → back (fore f) ≡ f
  retr f i t (vstrand g) = f t (vstrand g)
  retr f i t (vpoint e x) = f t (vpoint e x)
  retr f i t (vpath e g j) = f t (vpath e g j)

  thm : ((t : T) → View t → H t) ≅ Γ PushRec2
  thm = isoToEquiv (iso fore back sect retr) where


-- pr1 t .PushRec1.pr1f t v ≡ ah t e v
≅2 : Γ PushRec1 ≅ Γ PushRec3
≅2 = isoToEquiv (iso fore back sect retr) where
  fore : Γ PushRec1 → Γ PushRec3
  fore pr1 t = pushRec3 (≅1.fore (pr1 t .PushRec1.pr1f) t)
          λ e i v → ((λ i → (≅1.retr (pr1 t .PushRec1.pr1f)) i t v) ∙ (λ i → pr1 t .PushRec1.pr1a t e i v)) i

  back : Γ PushRec3 → Γ PushRec1
  back pp t = pushRec1 (λ t' x → {!!}) {!!}

  sect : (pp : Γ PushRec3) → fore (back pp) ≡ pp
  sect pp i = {!!}

  retr : (f : Γ PushRec1) → back (fore f) ≡ f
  retr = {!!}


-- fore : ( (Σ[ f ∈ ((t : T) → View t → H t) ] ((t : T)(e : E t) → f t ≡ ah t e)))
--         → (Σ[ f ∈ (Γ View → Γ H) ] ((t : T) (e : E t) (g : Γ View) → f g t ≡ ah t e (g t)))

-- fore (f , f') = (λ g t → f t (g t)) , λ t e g i → f' t e i (g t)

-- -- processView : (f  : Γ View → Γ H) (f' : (t : T) (e : E t) (g : Γ View) → f g t ≡ ah t e (g t))
-- --               (t : T) (v : View t) → H t

-- processView : (f  : Γ View → Γ H) (f' : (t : T) (e : E t) (g : Γ View) → f g t ≡ ah t e (g t))
--                (t : T) (v : View t) → H t
-- processView f f' t (vstrand g) = f (gg2vv g) t
-- processView f f' t v@(vpoint e x) = ah t e v
-- processView f f' t (vpath e g i) = {!f' t e (gg2vv g) i!}
-- -- ((λ i → f' t e (gg2vv g) i) ∙ {!!}) i

-- -- processView f f' t (vstrand g) = f g t
-- -- processView f f' t (vpoint e g) = ah t e g
-- -- processView f f' t (vpath e g i) = f' t e g i

-- -- processView' : (f  : Γ View → Γ H) (f' : (t : T) (e : E t) (g : Γ View) → f g t ≡ ah t e (g t))
-- --               (t : T) (e : E t) (g : View t) → processView f f' t (invIsEq (visEq t) g) ≡ ah t e g
-- -- processView' f f' t e g i with invIsEq (visEq t) g
-- -- processView' f f' t e g i | vstrand g' = {!f' t e g' i!}
-- -- processView' f f' t e g i | vpoint e' g' = {!!}
-- -- processView' f f' t e g i | vpath e' g' j = {!!}

-- back : (Σ[ f ∈ (Γ View → Γ H) ] ((t : T) (e : E t) (g : Γ View) → f g t ≡ ah t e (g t)))
--        → ( (Σ[ f ∈ ((t : T) → View t → H t) ] ((t : T)(e : E t) → f t ≡ ah t e)))
-- back (f , f') = (λ t g → processView f f' t g) , λ t e i g → {!!}
