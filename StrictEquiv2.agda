{-# OPTIONS --cubical --rewriting --allow-unsolved-metas  #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_ ; refl to reflp )
open import Cubical.Data.Equality using (ap) renaming (_∙_ to _∙p_ )
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath ; eqToPath-pathToEq)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv hiding (isEquiv')
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
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
 - Definition of isEquiv predicate on a function.
 -
 - It's not essential that I'm using (inductively defined equality) ≡p
 - here. The definition would be definitionally symmetric in all the
 - nice ways if I had used cubical equality ≡ or some pre-existing
 - notion ≅ of equivalence. But the proof that isEquiv' is a mere
 - proposition seemed to go much much easier when I could pattern
 - match on refl.
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
 iseq = isEquiv f
 iseq' = isEquiv' f

 invOfPath : ∀ {ℓ} {A B : Set ℓ} → A ≡p B → B → A
 invOfPath reflp x = x

 stage0 = iseq'

 stage1 : Set (ℓ-suc ℓ)
 stage1 = Σ[ eab ∈ (A ≡p B) ] (f ≡p getFunp eab)

 lemma0/1 : stage0 ≅ stage1
 lemma0/1 = isoToEquiv (iso fore back sect retr ) where
  fore : stage0 → stage1
  fore (mkIsEq R _ reflp erb pab reflp) = erb , pab

  back : stage1 → stage0
  back (erb , pab) = mkIsEq A (getInvp erb) reflp erb pab reflp

  sect : (e : stage1) → fore (back e) ≡ e
  sect (erb , pab) = refl

  retr : (e : stage0) → back (fore e) ≡ e
  retr (mkIsEq R _ reflp erb pab reflp) = refl

 univp1 : (A ≅ B) ≅ (A ≡ B)
 univp1 = invEquiv univalence

 univp2 : (A ≡ B) ≅ (A ≡p B)
 univp2 = isoToEquiv Cubical.Data.Equality.Conversion.PathIsoEq

 univp : (A ≅ B) ≅ (A ≡p B)
 univp = compEquiv univp1 univp2

 stage2 : Set (ℓ)
 stage2 = Σ[ eab ∈ Σ (A → B) isEquiv ] f ≡p getFunp (equivFun univp eab)

 lemma1/2 : stage1 ≅ stage2
 lemma1/2 = invEquiv (Σ-cong-equiv-fst univp)

 stage3 : Set (ℓ)
 stage3 = Σ[ eab ∈ Σ (A → B) isEquiv ] f ≡p fst eab

 -- This is an easy lemma that might be in a library somewhere already.
 concat-lemma : ∀ {ℓ} {A : Set ℓ} {a b c : A} → (b ≡p c) → (a ≡p b) ≅ (a ≡p c)
 concat-lemma {a = a} {b = b} reflp = idEquiv (a ≡p b)

 lemma2/3-match : (cp : A ≡p B) → getFunp cp ≡ transport (eqToPath cp)
 lemma2/3-match reflp = λ i z → transportRefl z (~ i)

 lemma2/3 : stage2 ≅ stage3
 lemma2/3 = Σ-cong-equiv-snd λ s → concat-lemma (pathToEq
     ((lemma2/3-match (pathToEq (ua s)) ∙ cong transport (eqToPath-pathToEq (ua s))) ∙ (λ i a → uaβ s a i)))

 lemma3/■ : stage3 ≅ iseq
 lemma3/■ = isoToEquiv (iso fore back sect retr) where
  fore : stage3 → iseq
  fore ((.f , fe) , reflp) = fe

  back : iseq → stage3
  back fe = ((f , fe) , reflp)

  sect : (e : iseq) → fore (back e) ≡ e
  sect e = refl

  retr : (e : stage3) → back (fore e) ≡ e
  retr ((.f , fe) , reflp) = refl

{---------------------------------------------------------------
 - Here it is:
 ---------------------------------------------------------------}
 isEquiv'IsProp : isProp iseq'
 isEquiv'IsProp = equivPresProp (invEquiv bigEq) (isPropIsEquiv f)
  where
  equivPresProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≅ B → isProp A → isProp B
  equivPresProp (f , fe) pa b1 b2 = sym (sec b1) ∙ cong f (pa (g b1) (g b2)) ∙ sec b2
   where
   g = invIsEq fe
   sec = secIsEq fe

  bigEq : iseq' ≅ iseq
  bigEq = iseq'
       ≃⟨ lemma0/1 ⟩ stage1
       ≃⟨ lemma1/2 ⟩ stage2
       ≃⟨ lemma2/3 ⟩ stage3
       ≃⟨ lemma3/■ ⟩ iseq
       ■
