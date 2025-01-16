{-# OPTIONS --cubical --rewriting --allow-unsolved-metas  #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_ ; pathToEquiv to p2e)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv hiding (isEquiv')
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module StrictEquiv2 where

infix 4 _≅'_

record isEquiv' {ℓ : Level} {A : Set ℓ} {B : Set ℓ} (mab : A → B) : Set (ℓ-suc ℓ) where
 field
  R : Set ℓ
  mba : B → A
  mra : R → A
  mrb : R → B
  era : isEquiv mra
  erb : isEquiv mrb
  pab : mab ≡ mrb ∘ (invIsEq era)
  pba : mba ≡ mra ∘ (invIsEq erb)

_≅'_ : {ℓ : Level} (A : Set ℓ) (B : Set ℓ) → Set (ℓ-suc ℓ)
A ≅' B = Σ (A → B) isEquiv'

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅' B) where
 private
  open isEquiv' (q .snd)
  mab = q .fst
  fra = funIsEq era
  frb = funIsEq erb
  ira = invIsEq era
  irb = invIsEq erb

 getFun : A → B
 getFun = frb ∘ ira

 getInv : B → A
 getInv = fra ∘ irb

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = cong frb (retIsEq era (irb b)) ∙ secIsEq erb b

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = cong fra (retIsEq erb (ira a)) ∙ secIsEq era a

 invert : B ≅' A
 invert = mba , (record
                  { R = R
                  ; mba = mab
                  ; mra = mrb
                  ; mrb = mra
                  ; era = erb
                  ; erb = era
                  ; pab = pba
                  ; pba = pab
                  })

module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅' B) where
 open isEquiv'

 invert-strict-inv : invert (invert q) ≡ q
 invert-strict-inv = refl

 invertPresFun : getFun q ≡ getInv (invert q)
 invertPresFun = refl

 invertPresInv : getInv q ≡ getFun (invert q)
 invertPresInv = refl

 invertPresRet : getRet q ≡ getSec (invert q)
 invertPresRet = refl

 invertPresSec : getSec q ≡ getRet (invert q)
 invertPresSec = refl

module _ {ℓ : Level} {A : Set ℓ} where
 reflEquiv : A ≅' A
 reflEquiv = (λ x → x) , record
                          { R = A
                          ; mba = λ x → x
                          ; mra = λ x → x
                          ; mrb = λ x → x
                          ; era = idIsEquiv A
                          ; erb = idIsEquiv A
                          ; pab = refl
                          ; pba = refl
                          }

 invertRefl : invert (reflEquiv) ≡ reflEquiv
 invertRefl = refl

equivPresProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≅ B → isProp A → isProp B
equivPresProp (f , fe) pa b1 b2 = sym (sec b1) ∙ cong f (pa (g b1) (g b2)) ∙ sec b2
 where
 g = invIsEq fe
 sec = secIsEq fe

module _ {ℓ : Level} {A B : Set ℓ} (f : A → B) where

{-
Informal proof
The record

  R : Set ℓ
  mba : B → A
  mra : R → A
  mrb : R → B
  era : isEquiv mra
  erb : isEquiv mrb
  pab : mab ≡ mrb ∘ (invIsEq era)
  pba : mba ≡ mra ∘ (invIsEq erb)

is iso (by J, by observing that pba fixes what mba must be) to

  R : Set ℓ
  mra : R → A
  mrb : R → B
  era : isEquiv mra
  erb : isEquiv mrb
  pab : mab ≡ mrb ∘ (invIsEq era)

which is iso (by combining mra and era) to

  R : Set ℓ
  iso-ra : R ≅ A
  mrb : R → B
  erb : isEquiv mrb
  pab : mab ≡ mrb ∘ (invOfIso iso-ra)

but by univalence that's iso to

  R : Set ℓ
  path-ra : R ≡ A
  mrb : R → B
  erb : isEquiv mrb
  pab : mab ≡ mrb ∘ (invOfPath path-ra)

so by J on R  path-ra, this is iso to

  mrb : A → B
  erb : isEquiv mrb
  pab : mab ≡ mrb

which by J on pab is iso to

  erb : isEquiv mab

which is a prop.

-}
 mab = f -- a synonym
 iseq = isEquiv f
 iseq' = isEquiv' f

 invOfPath : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
 invOfPath = {!!}

 record stage1 : Set (ℓ-suc ℓ) where
  field
   R : Set ℓ
   mra : R → A
   mrb : R → B
   era : isEquiv mra
   erb : isEquiv mrb
   pab : mab ≡ mrb ∘ (invIsEq era)

 record stage2 : Set (ℓ-suc ℓ) where
  field
   R : Set ℓ
   iso-ra : R ≅ A
   mrb : R → B
   erb : isEquiv mrb
   pab : mab ≡ mrb ∘ (invIsEq (iso-ra .snd))

 record stage3 : Set (ℓ-suc ℓ) where
  field
   R : Set ℓ
   path-ra : R ≡ A
   mrb : R → B
   erb : isEquiv mrb
   pab : mab ≡ mrb ∘ (invOfPath path-ra)

 record stage4 : Set (ℓ-suc ℓ) where
  field
   mrb : A → B
   erb : isEquiv mrb
   pab : mab ≡ mrb

 lemma01 : iseq' ≅ stage1
 lemma01 = {!!}

 lemma12 : stage1 ≅ stage2
 lemma12 = {!!}

 lemma23 : stage2 ≅ stage3
 lemma23 = {!!}

 lemma34 : stage3 ≅ stage4
 lemma34 = {!!}

 lemma4■ : stage4 ≅ iseq
 lemma4■ = {!!}

 isEquiv'IsProp : isProp iseq'
 isEquiv'IsProp = equivPresProp (invEquiv bigEq) (isPropIsEquiv f)
  where
  bigEq : iseq' ≅ iseq
  bigEq = iseq'
       ≃⟨ lemma01 ⟩ stage1
       ≃⟨ lemma12 ⟩ stage2
       ≃⟨ lemma23 ⟩ stage3
       ≃⟨ lemma34 ⟩ stage4
       ≃⟨ lemma4■ ⟩ iseq
       ■
