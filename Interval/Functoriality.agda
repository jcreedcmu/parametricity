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
 - There remains some stuff to be formulated and proved here.
 - Something like: a homomorphism between relations R1 and R2 is the same
 - thing as a map (t : T) → Gel R1 t → Gel R2 t
 -}
module Interval.Functoriality where

module _ {ℓ : Level} (D : Set ℓ) (S : Set ℓ) where
 private
  T = D ▻ S
  E = End


  module toOpen0 = Interval.Gel.main {ℓ} {ℓ} D S
  open toOpen0

  module _ {A1 : {t : T} (e : E t) → Set ℓ}
           {A2 : {t : T} (e : E t) → Set ℓ}
           (R1 R2 : Set ℓ)
           (disc-R2 : disc R2)
           (disc-EA2 : (t : T) → disc (Σ (E t) A2))
           (disc-ER2 : (t : T) → disc (E t × R2))
           (f1 : (r : R1) {t : T} (e : E t) → A1 e)
           (f2 : (r : R2) {t : T} (e : E t) → A2 e)
           (ah : {t : T} (e : E t) → A1 e → A2 e)
    where

    module toOpen1 = Interval.Gel.main.gel {ℓ} {ℓ} D S R1 f1
    open toOpen1 renaming (Gel to Gel1 ; gstrand to gstrand1 ; gpoint to gpoint1 ; gpath to gpath1 ; gel to gel1 )
    module toOpen2 = Interval.Gel.main.gel {ℓ} {ℓ} D S R2 f2
    open toOpen2 renaming (Gel to Gel2 ; gstrand to gstrand2 ; gpoint to gpoint2 ; gpath to gpath2 ; gel to gel2 )

    ungel2 : ((t : T) → Gel2 t) → R2
    ungel2 = toOpen2.ungel disc-R2 disc-EA2 disc-ER2

    relhom : Set ℓ
    relhom = Σ[ rh ∈ (R1 → R2) ] ({t : T} (e : E t) (r1 : R1) → ah e (f1 r1 e) ≡ f2 (rh r1) e)



    interglobal→relhom : (((t : T) → Gel1 t) → ((t : T) → Gel2 t)) → relhom
    interglobal→relhom igm = (λ r1 → ungel2 (igm (gel1 r1))) , {!!}

    Igm : Set (ℓ-max ℓ {!!})
    Igm = Σ[ igm ∈ (((t : T) → Gel1 t) → ((t : T) → Gel2 t)) ] {! {t : T} (e : E t) → igm m1 t!}

    fore : ((t : T) → Gel1 t → Gel2 t) → ((t : T) → Gel1 t) → ((t : T) → Gel2 t)
    fore um gm t = um t (gm t)
