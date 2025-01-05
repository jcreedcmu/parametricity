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
 - Practicing substituting isomorphisms into records that
 - constitute maps out of pushouts.
 -}
module Interval.PushoutWarmup2 (A : Set) (A' : Set) (B : Set) (C : Set) (f : C → A) (g : C → B)
  (into : A → A') (intoEq : isEquiv into) (H : Set)
  where

outo : A' → A
outo = invIsEq intoEq

isec : (a' : A') → into (outo a') ≡ a'
isec = secIsEq intoEq

iret : (a : A) → outo (into a) ≡ a
iret = retIsEq intoEq

record P : Set where
 constructor pp
 field
  pa : A → H
  pb : B → H
  pc : (c : C) → pa (f c) ≡ pb (g c)

record Q : Set where
 constructor qq
 field
  qa : A' → H
  qb : B → H
  qc : (c : C) → qa (into (f c)) ≡ qb (g c)

fore : P → Q
fore (pp pa pb pc) = qq (pa ∘ outo) pb λ c → (λ i → pa (iret (f c) i)) ∙ pc c

back : Q → P
back (qq qa qb qc) = pp (qa ∘ into) qb λ c → (λ i → qa (into (f c))) ∙ qc c

sect : (q : Q) → fore (back q) ≡ q
sect (qq qa qb qc) i = qq (λ a' → qa (isec a' i)) qb {!!}

-- -- i = i0 ⊢ pinr (g c)
-- -- i = i1 ⊢ pinl (invIsEq intoEq (into (f c)))
-- back : Q → P
-- back (pinl a) = pinl (outo a)
-- back (pinr b) = pinr b
-- back (ppath c i) = hcomp (λ j → λ {
--      (i = i0) → ppath c (~ j) ;
--      (i = i1) → pinl (retIsEq intoEq (f c) (~ j))
--    }) (pinl (f c))

-- -- (ppath c ∙ λ j → pinl (retIsEq intoEq (f c) (~ j)) ) i

-- -- Square top bot left right = PathP (λ y → left y ≡ right y) top bot

-- hardMap : (c : C) → PathP (λ i → fore (back (ppath c i)) ≡ (ppath c i))
--        (λ i → pinr (g c))
--        (λ i → pinl (secIsEq intoEq (into (f c)) i))
-- hardMap = {!!}

-- -- hfill (λ z → λ { (y = i0) → {!ppath c (~ z)!} ; (y = i1) → {!pinl (secIsEq intoEq (into (f c)) (~ z))!} }) (inS (pinl (into (f c)))) z

-- sqMap : (c : C) → Square (λ x → pinr (g c))
--                           (λ x → pinl (secIsEq intoEq (into (f c)) x))
--                           (λ y → fore (back (ppath c y)))
--                           (ppath c)
-- sqMap c y x = hcomp (λ (z : I) → λ {
--        (x = i0) → {!!} ;
--        (x = i1) → ppath c y ;
--        (y = i0) → ppath c (~ x ∧ ~ z) ;
--        (y = i1) → pinl (secIsEq intoEq (into (f c)) (x ∨ ~ z))
--      }) (ppath c (~ x ∨ y))

-- -- z = i0 ⊢ pinl (into (f c))
-- -- z = i1 ⊢ pinl (secIsEq intoEq (into (f c)) x)
-- -- x = i0 ⊢ ?1 (A = A) (A' = A') (B = B) (C = C) (f = f) (g = g)
-- --          (into = into) (intoEq = intoEq) (c = c) (y = i1) (z = z)
-- -- x = i1 ⊢ pinl (into (f c))

-- foo : (c : C) → pinr (g c) ≡ pinl (into (outo (into (f c)) ))
-- foo c x = fore (back (ppath c x))

-- sect : (q : Q) → fore (back q) ≡ q
-- sect (pinl a') i = pinl (secIsEq intoEq a' i)
-- sect (pinr b) i = pinr b
-- sect (ppath c i) = sqMap c i

-- sqMap2 : (c : C) → Square (λ x → pinr (g c))
--                            (λ x → pinl (retIsEq intoEq (f c) x))
--                            (λ y → back (fore (ppath c y)))
--                            (ppath c)
-- sqMap2 = {!!}

-- retr : (p : P) → back (fore p) ≡ p
-- retr (pinl a) i = pinl (retIsEq intoEq a i)
-- retr (pinr b) i = pinr b
-- retr (ppath c j) i = sqMap2 c j i

-- thm : P ≅ Q
-- thm = isoToEquiv (iso fore back sect retr)

-- -- i = i0 ⊢ (ppath c ∙ (λ j₁ → pinl (retIsEq intoEq (f c) (~ j₁)))) j
-- -- i = i1 ⊢ ppath c j
-- -- j = i0 ⊢ pinr (g c)
-- -- j = i1 ⊢ pinl (retIsEq intoEq (f c) i)

-- -- module _ (D : Q → Set)
-- --   (af : (a' : A') → D (pinl a'))
-- --   (bf : (b : B) → D (pinr b))
-- --   (cf : (c : C) → PathP (λ i → D (ppath c i)) (bf (g c)) (af (into (f c))))
-- --   where
-- --  Qelim : (q : Q)  → D q
-- --  Qelim (pinl a) = af a
-- --  Qelim (pinr b) = bf b
-- --  Qelim (ppath c i) = cf c i
