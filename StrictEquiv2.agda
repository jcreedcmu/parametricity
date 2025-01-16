{-# OPTIONS --cubical --rewriting --allow-unsolved-metas  #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_ ; refl to reflp)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv hiding (isEquiv')
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Function.Base
module StrictEquiv2 where

infix 4 _≅'_

module _ {ℓ : Level} {A : Set ℓ} {B : Set ℓ}  where

 getFunp : (q : A ≡p B) → A → B
 getFunp reflp x = x

 getInvp : (q : A ≡p B) → B → A
 getInvp reflp x = x

 getSecp : (q : A ≡p B) (b : B) → getFunp q (getInvp q b) ≡ b
 getSecp reflp b = refl

 getRetp : (q : A ≡p B) (a : A) → getInvp q (getFunp q a) ≡ a
 getRetp reflp b = refl

{-
 - Definition of isEquiv predicate on a function
 -}
record isEquiv' {ℓ : Level} {A : Set ℓ} {B : Set ℓ} (mab : A → B) : Set (ℓ-suc ℓ) where
 constructor mkIsEq
 field
  R : Set ℓ
  mba : B → A
  era : R ≡p A
  erb : R ≡p B
  pab : mab ≡p getFunp erb ∘ getInvp era
  pba : mba ≡p getFunp era ∘ getInvp erb

{-
 - Definition of equivalence relation between types.
 - Is the expected Σ type.
 -}

_≅'_ : {ℓ : Level} (A : Set ℓ) (B : Set ℓ) → Set (ℓ-suc ℓ)
A ≅' B = Σ (A → B) isEquiv'

{-
 - Useful accessors to get out the function, inverse, section, retraction
 - of an equivalence. Also define inversion.
 -}
module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅' B) where
 private
  open isEquiv' (q .snd)
  mab = q .fst
  fra = getFunp era
  frb = getFunp erb
  ira = getInvp era
  irb = getInvp erb

 getFun : A → B
 getFun = frb ∘ ira

 getInv : B → A
 getInv = fra ∘ irb

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = cong frb (getRetp (era) (irb b)) ∙ getSecp (erb) b

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = cong fra (getRetp (erb) (ira a)) ∙ getSecp (era) a

 invert : B ≅' A
 invert = mba , (record
                  { R = R
                  ; mba = mab
                  ; era = erb
                  ; erb = era
                  ; pab = pba
                  ; pba = pab
                  })

{-
 - Inversion is a strict involution.
 - Strict exchange of function ↔ inverse, section ↔ retraction,
 -}
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

{-
 - The reflexivity equivalence is strictly preserved by inversion.
 -}
module _ {ℓ : Level} {A : Set ℓ} where
 reflEquiv : A ≅' A
 reflEquiv = (λ x → x) , record
                          { R = A
                          ; mba = λ x → x
                          ; era = reflp
                          ; erb = reflp
                          ; pab = reflp
                          ; pba = reflp
                          }

 invertRefl : invert (reflEquiv) ≡ reflEquiv
 invertRefl = refl

{---------------------------------------------------------------
 - Finally, we show that isEquiv' is a proposition.
 ---------------------------------------------------------------}

module _ {ℓ : Level} {A B : Set ℓ} (f : A → B) where

{-
Proof sketch:

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

 invOfPath : ∀ {ℓ} {A B : Set ℓ} → A ≡p B → B → A
 invOfPath reflp x = x

 stage0 = iseq'

 record stage1 : Set (ℓ-suc ℓ) where
  constructor c1
  field
   erb : A ≡p B
   pab : mab ≡p getFunp erb

 lemma0/1 : stage0 ≅ stage1
 lemma0/1 = isoToEquiv (iso fore back sect retr ) where
  fore : stage0 → stage1
  fore (mkIsEq R _ reflp erb pab reflp) = c1 erb pab

  back : stage1 → stage0
  back (c1 erb pab) = mkIsEq A (getInvp erb) reflp erb pab reflp

  sect : (e : stage1) → fore (back e) ≡ e
  sect (c1 erb pab) = refl

  retr : (e : stage0) → back (fore e) ≡ e
  retr (mkIsEq R _ reflp erb pab reflp) = refl

 -- record stage3 : Set (ℓ-suc ℓ) where
 --  constructor c3
 --  field
 --   R : Set ℓ
 --   path-ra : R ≡p A
 --   mrb : R → B
 --   erb : isEquiv mrb
 --   pab : mab ≡ mrb ∘ (invOfPath path-ra)

 -- lemma2/3 : stage2 ≅ stage3
 -- lemma2/3 = {!!} -- by univalence

 -- stage3a : Set ℓ
 -- stage3a = Σ[ mrb ∈ (A → B) ] (isEquiv mrb × (mab ≡ mrb))

 -- lemma3/3a : stage3 ≅ stage3a
 -- lemma3/3a = isoToEquiv (iso fore back sect retr) where
 --  fore : stage3 → stage3a
 --  fore (c3 .A reflp mrb erb pab) = mrb , (erb , pab)

 --  back : stage3a → stage3
 --  back (mrb , erb , pab) = c3 A reflp mrb erb pab

 --  sect : (e : stage3a) → fore (back e) ≡ e
 --  sect (mrb , erb , pab) = refl

 --  retr : (e : stage3) → back (fore e) ≡ e
 --  retr (c3 .A reflp mrb erb pab) = refl

 -- stage4 : Set ℓ
 -- stage4 = Σ[ mrb ∈ (A → B) ] (isEquiv mrb × (mab ≡p mrb))

 -- lemma3a/4 : stage3a ≅ stage4
 -- lemma3a/4 = Σ-cong-equiv (idEquiv (A → B)) λ mrb →
 --              Σ-cong-equiv (idEquiv (isEquiv mrb)) λ _ →
 --              (isoToEquiv Cubical.Data.Equality.Conversion.PathIsoEq)

 -- lemma4/■ : stage4 ≅ iseq
 -- lemma4/■ = isoToEquiv (iso fore back sect retr) where
 --  fore : stage4 → iseq
 --  fore (_ , (erb , reflp)) = erb

 --  back : iseq → stage4
 --  back e = (f , (e , reflp))

 --  sect : (e : iseq) → fore (back e) ≡ e
 --  sect e = refl

 --  retr : (e : stage4) → back (fore e) ≡ e
 --  retr (_ , (_ , reflp)) = refl

 -- isEquiv'IsProp : isProp iseq'
 -- isEquiv'IsProp = equivPresProp (invEquiv bigEq) (isPropIsEquiv f)
 --  where
 --  equivPresProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≅ B → isProp A → isProp B
 --  equivPresProp (f , fe) pa b1 b2 = sym (sec b1) ∙ cong f (pa (g b1) (g b2)) ∙ sec b2
 --   where
 --   g = invIsEq fe
 --   sec = secIsEq fe

 --  bigEq : iseq' ≅ iseq
 --  bigEq = iseq'
 --       ≃⟨ lemma■/0 ⟩ stage0
 --       ≃⟨ lemma0/1 ⟩ stage1
 --       ≃⟨ lemma1/2 ⟩ stage2
 --       ≃⟨ lemma2/3 ⟩ stage3
 --       ≃⟨ lemma3/3a ⟩ stage3a
 --       ≃⟨ lemma3a/4 ⟩ stage4
 --       ≃⟨ lemma4/■ ⟩ iseq
 --       ■
