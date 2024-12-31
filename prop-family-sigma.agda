{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv ; equivFun)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude renaming (_≡_ to _≡c_ ; i0 to ci0 ; i1 to ci1 ; I to cI)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module prop-family-sigma where

-- couple of general lemmas
lemma8 : ∀ {ℓ} {G : Set ℓ} (a b c : G) (f : a ≡c c) (g : a ≡c b) (h : b ≡c c) →
   Square f h g (λ _ → c) → Square (λ _ → a) h g f
lemma8 a b c f g h x u t = hcomp ((λ v → λ {
  (u = ci0) → f (~ v ∧ t) ;
  (u = ci1) → h t ;
  (t = ci0) → g u ;
  (t = ci1) → f (~ v ∨ u)
  })) (x u t)

lemma' : ∀ {ℓ} {E : Set} {G : Set ℓ}  (e0 e1 : E) (p : e0 ≡c e1) (g : G) (h : E → G) (q : (e : E) → h e ≡c g) →
  PathP (λ t → h e0 ≡c q e1 t) (λ u → h (p u)) (λ u → q e0 u)
lemma' e0 e1 p g h q t u = lemma8 (h e0) (h e1) g (λ u → q e0 u) (λ u → h (p u)) (λ t → q e1 t) (λ u → q (p u)) u t

module propLem3 {ℓ k : Level} (E : Set ℓ) (A B : E → Set k) (E-isProp : isProp E)
       (fs : (Σ[ e ∈ E ] A e) → (Σ[ e ∈ E ] B e)) (ns : (Σ[ e ∈ E ] B e) → (Σ[ e ∈ E ] A e))
       (section-in : (eb : Σ[ e ∈ E ] B e) → fs (ns eb) ≡c eb) where

    cvt : (AorB : E → Set k) (src : E) (tgt : E) → AorB src → AorB tgt
    cvt AorB src tgt x = transport (λ t → AorB (E-isProp src tgt t)) x

    fore : {e : E} → A e → B e
    fore {e} a = let (e' , b) = fs (e , a) in cvt B e' e b

    back : {e : E} → B e → A e
    back {e} b = let (e' , a) = ns (e , b) in cvt A e' e a

    section6 : {x y : Σ[ e ∈ E ] B e} (p : y ≡c x) → transport (λ t → B (fst (p t))) (snd y) ≡c snd x
    section6 {x} {y} p u = transp (λ t → B (fst (p (t ∨ u)))) u (snd (p u))

    section5 : {x y : Σ[ e ∈ E ] B e} (p : y ≡c x) → (λ t → fst (p t)) ≡c E-isProp (fst y) (fst x)
    section5 {x} {y} p  = isProp→isSet E-isProp (fst y) (fst x) (λ t → fst (p t)) (E-isProp (fst y) (fst x))

    section4 : {x y : Σ[ e ∈ E ] B e} → y ≡c x → cvt B (fst y) (fst x) (snd y) ≡c snd x
    -- section4 : {x y : Σ[ e ∈ E ] B e} → y ≡c x → transport (λ t → B (E-isProp (fst y) (fst x) t)) (snd y) ≡c snd x
    section4 {x} {y} p  =  transport (λ v → (transport (λ t → B (section5 p v t)) (snd y) ≡c snd x)) (section6 p)

    section3 : (ea : Σ[ e ∈ E ] A e) (e' : E) → (e' , cvt A (fst ea) e' (snd ea)) ≡c  ea
    section3 ea e' u = (E-isProp (ea .fst) e' (~ u)) , transp (λ t → A (E-isProp (ea .fst) e' (t ∧ ~ u))) u (snd ea)

    section2 : (eb : Σ[ e ∈ E ] B e) → (fs (eb .fst , cvt A (fst (ns eb)) (eb .fst) (snd (ns eb)))) ≡c eb
    section2 eb  = (λ u → fs (section3 (ns eb) (eb .fst) u)) ∙ section-in eb

    out : {e : E} (b : B e) → fore (back b) ≡c b
    out {e} b u = section4 (section2 (e , b)) u

module propLem2 {ℓ k : Level} (E : Set ℓ) (A B : E → Set k) (E-isProp : isProp E) (sumeq : (Σ[ e ∈ E ] A e) ≅ (Σ[ e ∈ E ] B e)) where
    sumIsEq : isEquiv (equivFun sumeq)
    sumIsEq = snd sumeq
    fs = funIsEq sumIsEq
    ns = invIsEq sumIsEq

    cvt : (AorB : E → Set k) (src : E) (tgt : E) → AorB src → AorB tgt
    cvt AorB src tgt x = transport (λ t → AorB (E-isProp src tgt t)) x

    fore : {e : E} → A e → B e
    fore {e} a = let (e' , b) = fs (e , a) in cvt B e' e b

    back : {e : E} → B e → A e
    back {e} b = let (e' , a) = ns (e , b) in cvt A e' e a

    section : {e : E} (b : B e) → fore (back b) ≡c b
    section {e} b  = propLem3.out  E A B E-isProp fs ns (secIsEq sumIsEq) b

    retract : {e : E} (a : A e) → back (fore a) ≡c a
    retract {e} a  = propLem3.out  E B A E-isProp ns fs (retIsEq sumIsEq) a

    out : (e : E) → A e ≅ B e
    out e = isoToEquiv (Cubical.Foundations.Isomorphism.iso fore back section retract)

-- The interval
module _ (I : Set) (E : I → Set) (E-isProp : {i : I} → isProp (E i)) where

  E-redRefl : {i : I} (x : E i) → E-isProp x x ≡c (λ _ → x)
  E-redRefl {i} x = ((isProp→isSet E-isProp x x) (E-isProp x x) (λ _ → x))

  module pushout {ℓ : Level} {A : {i : I} (e : E i) → Set ℓ} (R : ({i : I} (e : E i) → A e) → Set ℓ) where

    data Gel : (i : I) → Set ℓ where
      gel : {a : {i : I} (e : E i) → A e} (r : R a) (i : I) → Gel i
      gelι : {i : I} {e : E i} (ae : A e) → Gel i
      gelιp : {i : I} {e : E i} (a : {i : I} (e : E i) → A e) (r : R a) → gelι (a e) ≡c gel r i

    extract-e : {i : I} {e : E i} → Gel i → E i
    extract-e {i} {e} (gel {a} r .i) = e
    extract-e {i} {e} (gelι {e = e'} ae) = e'
    extract-e {i} {e} (gelιp {e = e'} a r t) = E-isProp e' e t

    extract : {i : I} {e : E i} (g : Gel i) → A (extract-e {i} {e} g)
    extract {i} {e} (g @ (gel {a} r _)) = a e
    extract (gelι ae) = ae
    extract {i} {e} (g @ (gelιp {e = e'} a r t)) = a (E-isProp e' e t)

    fore : {i : I} → Σ[ e/ ∈ E i ] Gel i → Σ[ e/ ∈ E i ] A e/
    fore (e/ , g/) = (extract-e {e = e/} g/ , extract g/ )

    back : {i : I} → (Σ[ e/ ∈ E i ] A e/) → Σ[ e/ ∈ E i ] Gel i
    back (e/ , a/) = e/ , (gelι a/)

    section : {i : I} (b : Σ[ e/ ∈ E i ] A e/) → fore (back b) ≡c b
    section s t = s

    lemma : {a : {i : I} (e : E i) → A e} (r : R a) {i : I} (e/ e' : E i) (p : e' ≡c e/) →
      PathP (λ t → gelι (a e') ≡c gelιp {e = e/} a r t) (λ u → gelι (a (p u))) (λ u → gelιp {e = e'} a r u)
    lemma {a} r {i} e/ e' p = lemma' e' e/ p (gel r i) (gelι ∘ a) (λ x → gelιp {e = x} a r)

    retract : {i : I} (b : Σ[ e/ ∈ E i ] Gel i) → back (fore b) ≡c b
    retract (e/ , (gel {a} r i)) t = (e/ , gelιp {e = e/} a r t)
    retract (e/ , (gelι {e = e'} ae)) t = (E-isProp e' e/ t ,  gelι ae)
    retract (e/ , (gelιp {e = e'} a r u)) t = (E-isProp e' e/ (t ∨ u) , lemma {a} r e/ e' (E-isProp e' e/) t u)

    sumeq : {i : I} → (Σ[ e ∈ E i ] Gel i) ≅ (Σ[ e ∈ E i ] A e)
    sumeq = isoToEquiv (Cubical.Foundations.Isomorphism.iso fore back section retract)

    G-endpoints : {i : I} (e : E i) → Gel i ≅ A e
    G-endpoints {i} e = propLem2.out (E i) (λ _ → Gel i) A E-isProp sumeq e
