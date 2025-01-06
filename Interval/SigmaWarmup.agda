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
open import Cubical.Data.Sigma.Properties as Sprop
import Interval.Gel

{-
 - Practicing substituting isomorphisms into records that
 - constitute maps out of pushouts.
 -}
module Interval.SigmaWarmup (A : Set) (A' : Set)
  (into : A → A') (intoEq : isEquiv into) (D : A' → Set)
  where

outo : A' → A
outo = invIsEq intoEq

isec : (a' : A') → into (outo a') ≡ a'
isec = secIsEq intoEq

iret : (a : A) → outo (into a) ≡ a
iret = retIsEq intoEq


fore : Σ A (D ∘ into) → Σ A' D
fore (a , d) = into a , d

back : Σ A' D → Σ A (D ∘ into)
back (a' , d) = (outo a') , subst D (sym (isec a')) d

sect : (p : Σ A' D) → fore (back p) ≡ p
sect x = secIsEq (Sprop.Σ-cong-equiv-fst {A = A} {B = D} (into , intoEq) .snd) x

retr : (p : Σ A (D ∘ into)) → back (fore p) ≡ p
retr x = retIsEq (Sprop.Σ-cong-equiv-fst {A = A} {B = D} (into , intoEq) .snd) x

sect-lemma : (a' : A') (d : D a') → PathP (λ i → D (isec a' i)) (subst D (sym (isec a')) d) d
sect-lemma a' d i  = transp (λ j → D (isec a' (i ∨ ~ j))) i d

sect-mine : (p : Σ A' D) → fore (back p) ≡ p
sect-mine (a' , d) i = isec a' i , sect-lemma a' d i


PathP-to-transport : {A : I → Set} (x : A i0) (y : A i1) → PathP A x y → x ≡ transport (λ i → A (~ i)) y
PathP-to-transport {A} x y p i = transp (λ j → A (i ∧ ~ j)) (~ i) (p i)

transport-to-PathP : {A : I → Set} (x : A i0) (y : A i1) → x ≡ transport (λ i → A (~ i)) y → PathP A x y
transport-to-PathP {A} x y t i = {!!}

retr-lemma : (a : A) (d : D (into a)) → PathP (λ i → (D ∘ into) (iret a i)) (subst D (sym (isec (into a))) d) d
retr-lemma a d i = hcomp {!!} (transport  (λ j → D (snd (intoEq .equiv-proof (into a) .snd (a , (λ i₂ → into a)) i) (~ j)))  d)

blah : (a : A) → fst (intoEq .equiv-proof (into a)) ≡ (a , (λ _ → into a))
blah a = intoEq .equiv-proof (into a) .snd (a , (λ _ → into a))

blah' : (a : A) → fst (intoEq .equiv-proof (into a)) ≡ (a , (λ _ → into a))
blah' a = {!intoEq .equiv-proof (into a) .snd !}

out-fact : (a' : A') → outo a' ≡ intoEq .equiv-proof a' .fst .fst
out-fact a' i = outo a'

ret-fact : (a : A) → iret a ≡ λ i → fst (intoEq .equiv-proof (into a) .snd (a , (λ _ → into a)) i )
ret-fact a i = iret a

sec-fact : (a' : A') → isec a' ≡ intoEq .equiv-proof a' .fst .snd
sec-fact a' i = isec a'

-- ctrP = symP (transport-filler (λ i → B (sym α i)) b)

retr-mine : (p : Σ A (D ∘ into)) → back (fore p) ≡ p
retr-mine (a , d) i =  iret a i , retr (a , d) i .snd
-- fst (intoEq .equiv-proof (into (fst x)) .snd  (fst x , (λ i₁ → into (fst x))) i) , (retr x i .snd)

mmap : Σ A (D ∘ into) → Σ A' D
mmap x = Sprop.Σ-cong-equiv-fst (into , intoEq) .fst x

mmapi : Σ A' D → Σ A (D ∘ into)
mmapi x = invIsEq (Sprop.Σ-cong-equiv-fst (into , intoEq) .snd) x

foo : (x : Σ A' D) → mmapi x ≡ back x
foo x = refl

bar : (x : Σ A (D ∘ into)) → mmap x ≡ fore x
bar x = refl
