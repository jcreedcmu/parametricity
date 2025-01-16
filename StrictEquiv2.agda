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

{-
 - Definition of isEquiv predicate on a function, bootstrapped off an existing one.
 -}
record isEquiv' {ℓ : Level} {A : Set ℓ} {B : Set ℓ} (mab : A → B) : Set (ℓ-suc ℓ) where
 constructor mkIsEquiv
 field
  R : Set ℓ
  mba : B → A
  era : R ≅ A
  erb : R ≅ B
  pab : mab ≡p (erb .fst) ∘ (invIsEq (era .snd))
  pba : mba ≡p (era .fst) ∘ (invIsEq (erb .snd))

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
  fra = funIsEq (era .snd)
  frb = funIsEq (erb .snd)
  ira = invIsEq (era .snd)
  irb = invIsEq (erb .snd)

 getFun : A → B
 getFun = frb ∘ ira

 getInv : B → A
 getInv = fra ∘ irb

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = cong frb (retIsEq (era .snd) (irb b)) ∙ secIsEq (erb .snd) b

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = cong fra (retIsEq (erb .snd) (ira a)) ∙ secIsEq (era .snd) a

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
                          ; era = (λ x → x) , idIsEquiv A
                          ; erb = (λ x → x) , idIsEquiv A
                          ; pab = reflp
                          ; pba = reflp
                          }

 invertRefl : invert (reflEquiv) ≡ reflEquiv
 invertRefl = refl

{---------------------------------------------------------------
 - Finally, we show that isEquiv' is a proposition.
 ---------------------------------------------------------------}

module _ {ℓ : Level} {A B : Set ℓ} (f : A → B) where
 mab = f -- a synonym
 iseq = isEquiv f
 iseq' = isEquiv' f

 invOfPath : ∀ {ℓ} {A B : Set ℓ} → A ≡p B → B → A
 invOfPath reflp x = x

 stage0 = isEquiv' f
 stage4 = isEquiv f

 record stage1 : Set (ℓ-suc ℓ) where
  constructor c1
  field
   R : Set ℓ
   era : R ≅ A
   erb : R ≅ B
   pab : mab ≡p (erb .fst) ∘ (invIsEq (era .snd))

 lemma0/1 : stage0 ≅ stage1
 lemma0/1 = isoToEquiv (iso fore back sect retr) where
  fore : stage0 → stage1
  fore (mkIsEquiv R _ era erb pab reflp) = c1 R era erb pab

  back : stage1 → stage0
  back (c1 R era erb pab) = (mkIsEquiv R _ era erb pab reflp)

  sect : (e : stage1) → fore (back e) ≡ e
  sect (c1 R era erb pab) = refl

  retr : (e : stage0) → back (fore e) ≡ e
  retr (mkIsEquiv R _ era erb pab reflp) = refl

 tail : (R : Set ℓ) (e : R ≅ A) → Set ℓ
 tail R e = Σ[ erb ∈ (R ≅ B) ] (mab ≡p (erb .fst) ∘ (invIsEq (e .snd)))

 stage2 : Set (ℓ-suc ℓ)
 stage2 = Σ[ R ∈ Set ℓ ] Σ[ e ∈ R ≅ A ] (tail R e)

 lemma1/2 : stage1 ≅ stage2
 lemma1/2 = isoToEquiv (iso fore back sect retr) where
  fore : stage1 → stage2
  fore (c1 R era erb pab) = R , (era , (erb , pab))

  back : stage2 → stage1
  back (R , (era , (erb , pab))) = (c1 R era erb pab)

  sect : (e : stage2) → fore (back e) ≡ e
  sect (R , (era , (erb , pab))) = refl

  retr : (e : stage1) → back (fore e) ≡ e
  retr (c1 R era erb pab) = refl

 J-like : (X : (R : Set ℓ) (e : R ≅ A) → Set ℓ) → Set (ℓ-suc ℓ)
 J-like X = (Σ[ R ∈ Set ℓ ] Σ[ e ∈ R ≅ A ] X R e) ≅ (X A (idEquiv A))

 ΣJ : {B : (R : Set ℓ) (e : R ≅ A) → Set ℓ}
      {C : (R : Set ℓ) (e : R ≅ A) → B R e → Set ℓ}
      --                     vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv this type is wrong surely...
      (JB : J-like B) (JC : (b : (R : Set ℓ) (e : R ≅ A) → B R e) → J-like λ R e → C R e (b R e))
      → J-like (λ R e → Σ (B R e) (λ b → C R e b))
 ΣJ = {!!}

 RBJ : J-like (λ R e → R ≅ B)
 RBJ = {!!}


 tail-J : J-like tail
 tail-J = {!!}

 stage3 : Set ℓ
 stage3 = (tail A (idEquiv A))

 lemma2/3 : stage2 ≅ stage3
 lemma2/3 = tail-J

 -- stage3' : Set ℓ
 -- stage3' = Σ[ erb ∈ (A ≅ B) ] (mab ≡p (erb .fst))

 -- lemma3/3' : stage3 ≅ stage3'
 -- lemma3/3' = idEquiv _

 lemma3/4 : stage3 ≅ stage4
 lemma3/4 = isoToEquiv (iso fore back sect retr) where
  fore : stage3 → stage4
  fore ((.f , fe) , reflp) = fe

  back : stage4 → stage3
  back fe = ((f , fe) , reflp)

  sect : (e : stage4) → fore (back e) ≡ e
  sect fe = refl

  retr : (e : stage3) → back (fore e) ≡ e
  retr ((.f , fe) , reflp) = refl

 isEquiv'IsProp : isProp iseq'
 isEquiv'IsProp = equivPresProp (invEquiv bigEq) (isPropIsEquiv f)
  where
  equivPresProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≅ B → isProp A → isProp B
  equivPresProp (f , fe) pa b1 b2 = sym (sec b1) ∙ cong f (pa (g b1) (g b2)) ∙ sec b2
   where
   g = invIsEq fe
   sec = secIsEq fe

  bigEq : iseq' ≅ iseq
  bigEq = stage0
       ≃⟨ lemma0/1 ⟩ stage1
       ≃⟨ lemma1/2 ⟩ stage2
       ≃⟨ lemma2/3 ⟩ stage3
       ≃⟨ lemma3/4 ⟩ stage4
       ■
