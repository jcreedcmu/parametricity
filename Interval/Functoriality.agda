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

module Interval.Functoriality where

module _ {ℓ1 ℓ2 : Level} (D : Set ℓ1) (S : Set ℓ2) where
 private
  ℓ = ℓ-max ℓ1 ℓ2
  T = D ▻ S
  E = End

  open Interval.Gel.main {ℓ1} {ℓ2} D S

  module _ {A1 : {t : T} (e : E t) → Set ℓ1}
           {A2 : {t : T} (e : E t) → Set ℓ1}
           (R1 R2 : Set ℓ)
           (disc-R2 : disc R2)
           (disc-EA2 : (t : T) → disc (Σ (E t) A2))
           (disc-ER2 : (t : T) → disc (E t × R2))
           (f1 : (r : R1) {t : T} (e : E t) → A1 e)
           (f2 : (r : R2) {t : T} (e : E t) → A2 e)
           (ah : {t : T} (e : E t) → A1 e → A2 e)
    where

    relhom : Set (ℓ1 ⊔ ℓ2)
    relhom = Σ[ rh ∈ (R1 → R2) ] ({t : T} (e : E t) (r1 : R1) → ah e (f1 r1 e) ≡ f2 (rh r1) e)

    ungel2 = ungel R2 f2 disc-R2 disc-EA2 disc-ER2

    interglobal→relhom : (((t : T) → Gel R1 f1 t) → ((t : T) → Gel R2 f2 t)) → relhom
    interglobal→relhom igm = (λ r1 → ungel2 (igm (gel R1 f1 r1))) , {!!}

    Igm : Set {!!}
    Igm = Σ[ igm ∈ (((t : T) → Gel R1 f1 t) → ((t : T) → Gel R2 f2 t)) ] {! {t : T} (e : E t) → igm m1 t!}

    fore : ((t : T) → Gel R1 f1 t → Gel R2 f2 t) → ((t : T) → Gel R1 f1 t) → ((t : T) → Gel R2 f2 t)
    fore um gm t = um t (gm t)

    back : (((t : T) → Gel R1 f1 t) → ((t : T) → Gel R2 f2 t)) → ((t : T) → Gel R1 f1 t → Gel R2 f2 t)
    back g2m t (gstrand r) = g2m (λ t → gstrand r) t
    back g2m t (gpoint a) = {!!}
    back g2m t (gpath r i) = {!!}
