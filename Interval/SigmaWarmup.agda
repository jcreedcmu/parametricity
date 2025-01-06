{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
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
sect (a' , d) i = isec a' i , transp (λ j → D (isec a' (i ∨ ~ j))) i d

retr-lemma : (a : A) (d : D (into a)) → PathP (λ i → (D ∘ into) (iret a i)) (subst D (sym (isec (into a))) d) d
retr-lemma a d = toPathP⁻ (λ j → transport (λ i → D ( commPathIsEq intoEq a j (~ i) )) d)

retr : (p : Σ A (D ∘ into)) → back (fore p) ≡ p
retr (a , d) i =  iret a i ,  retr-lemma a d i

thm : Σ A (D ∘ into) ≅ Σ A' D
thm = isoToEquiv (iso fore back sect retr)

-- sect : (p : Σ A' D) → fore (back p) ≡ p
-- sect x = secIsEq (Sprop.Σ-cong-equiv-fst {A = A} {B = D} (into , intoEq) .snd) x

-- retr : (p : Σ A (D ∘ into)) → back (fore p) ≡ p
-- retr x = retIsEq (Sprop.Σ-cong-equiv-fst {A = A} {B = D} (into , intoEq) .snd) x

-- mmap : Σ A (D ∘ into) → Σ A' D
-- mmap x = Sprop.Σ-cong-equiv-fst (into , intoEq) .fst x

-- mmapi : Σ A' D → Σ A (D ∘ into)
-- mmapi x = invIsEq (Sprop.Σ-cong-equiv-fst (into , intoEq) .snd) x

-- foo : (x : Σ A' D) → mmapi x ≡ back x
-- foo x = refl

-- bar : (x : Σ A (D ∘ into)) → mmap x ≡ fore x
-- bar x = refl
