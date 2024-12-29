{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (sym ; _∙_ ; isContr ; transport ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module scratch where

-- The interval

postulate
  I : Set
  i0 i1 : I

-- Convenience type for maps 𝕀 → A with specified endpoints

module _ {ℓ : Level} (A : I → Set ℓ) where
  postulate
    Bridge : A i0 → A i1 → Set ℓ

postulate
  Bridge-self-isContr : isContr (Bridge (λ _ → I) i0 i1)
  Bridge-rev-isEmpty : ¬ (Bridge (λ _ → I) i1 i0)

Bridge-nontriv : ¬ (i1 ≡c i0)
Bridge-nontriv = {!!}

module _ {ℓ : Level} {A : I → Set ℓ} where
  postulate
    pabs : (f : (i : I) → A i) → Bridge A (f i0) (f i1)
    papp : {a0 : A i0} {a1 : A i1} → Bridge A a0 a1 → (i : I) → A i
    pβ : (f : (i : I) → A i) (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    pβ0 : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → papp p i0 ≡ a0
    {-# REWRITE pβ0 #-}
    pβ1 : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → papp p i1 ≡ a1
    {-# REWRITE pβ1 #-}
    pη : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → pabs (λ i → papp p i) ≡ p
    {-# REWRITE pη #-}

-- A type is bridge discrete if the constant combinator A → I → A is
-- an equivalence
bridge-discrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
bridge-discrete A = isEquiv λ (a : A) (i : I) → a

module sfunc {ℓ : Level} {A B : Set ℓ} (R : A → B → Set ℓ) where

  record total : Set ℓ where
   field
    ea : A
    eb : B
    er : R ea eb

  data Gel : (i : I) → Set ℓ where
    gel : {a : A} {b : B} (r : R a b) (i : I) → Gel i
    gel0 : (a : A) → Gel i0
    gel1 : (b : B) → Gel i1
    gel0p : (a : A) {b : B} (r : R a b) → gel r i0 ≡c gel0 a
    gel1p : {a : A} (b : B) (r : R a b) → gel r i1 ≡c gel1 b

  bgel : {a : A} {b : B} (r : R a b) → Bridge Gel (gel0 a) (gel1 b)
  bgel {a} {b} r = transport (λ t → Bridge Gel (gel0p a r t) (gel1p b r t)) (pabs (gel r))

  module _ (bd : bridge-discrete total) where

    postulate
      bgel-isEquiv : {a : A} {b : B} → isEquiv (bgel {a} {b})

    ungel : {a : A} {b : B} → Bridge Gel (gel0 a) (gel1 b) → R a b
    ungel p = invIsEq bgel-isEquiv p

    Gelβ : {a : A} {b : B} (r : R a b) → ungel (bgel r) ≡ r
    Gelβ r = pathToEq (retIsEq bgel-isEquiv r)

    Gelη : {a : A} {b : B} (p : Bridge Gel (gel0 a) (gel1 b)) (i : I) → bgel (ungel p) ≡ p
    Gelη p i = pathToEq (secIsEq bgel-isEquiv p)

    module dpush {Q : I → Set ℓ} (qa : A → Q i0) (qb : B → Q i1)
                 (qf : {a : A} {b : B} (r : R a b) → Bridge Q (qa a) (qb b)) where
       pmap : (i : I) → Gel i → Q i
       pmap i (gel r .i) = papp (qf r) i
       pmap .i0 (gel0 a) = qa a
       pmap .i1 (gel1 b) = qb b
       pmap .i0 (gel0p a r i) = qa a
       pmap .i1 (gel1p b r i) = qb b

  -- Trying to show that Gel i0 is A

  postulate
    cvtA : A → (i0 ≡c i0) → A
    cvtA/ : (a : A) → cvtA a (λ _ → i0) ≡c a
    cvtB : B → (i1 ≡c i0) → A
    cvt : {a : A} {b : B} → R a b → Bridge (λ i → i ≡c i0 → A) (cvtA a) (cvtB b)

  fore : (i : I) → Gel i → (i ≡c i0) → A
  fore i (gel r .i) p = papp (cvt r) i p
  fore .i0 (gel0 a) p = cvtA a p
  fore .i1 (gel1 b) p = cvtB b p
  fore .i0 (gel0p a r i) p = cvtA a p
  fore .i1 (gel1p b r i) p = cvtB b p

  fore' : Gel i0 → A
  fore' g = fore i0 g (λ _ → i0)

  retract' : (i : I) (a : Gel i) (p : i ≡c i0) → gel0 (fore i a p) ≡c transport (λ t → Gel (p t)) a
  retract' i (gel r .i) p = {!!}
  retract' .i0 (gel0 a) p = {!!}
  retract' .i1 (gel1 b) p = {!!}
  retract' .i0 (gel0p a r i) p = {!!}
  retract' .i1 (gel1p b r i) p = {!!}

  retract : (a : Gel i0) → gel0 (fore i0 a (λ _ → i0)) ≡c a
  retract a = retract' i0 a (λ _ → i0) ∙ Cubical.Foundations.Prelude.transportRefl a

  Gel0≡A' : Gel i0 ≅ A
  Gel0≡A' = isoToEquiv (Cubical.Foundations.Isomorphism.iso fore' gel0 cvtA/ retract)


  abort : (p : i1 ≡c i0) {A : Set ℓ} → A
  abort p {A} = Cubical.Data.Empty.elim {A = λ _ → A} (Bridge-nontriv p)


  Gel0≡A-fore-case : (i : I) → Gel i → i ≡c i0 → A
  Gel0≡A-fore-case .i (gel {a} r i) p = a
  Gel0≡A-fore-case .i0 (gel0 a) p = a
  Gel0≡A-fore-case .i1 (gel1 b) p = abort p
  Gel0≡A-fore-case .i0 (gel0p a r i) p = a
  Gel0≡A-fore-case .i1 (gel1p {a} b r i) p = abort p {a ≡c abort p} i

  Gel0≡A-fore : Gel i0 → A
  Gel0≡A-fore g = Gel0≡A-fore-case i0 g (λ _ → i0)

  retr-lemma2 : (i : I) {G : I → Set ℓ} {g : (i : I) → G i} (p : i ≡c i0) →  g i0 ≡c transport (λ t → G (p t)) (g i)
  retr-lemma2 = {!!}

  refli0 : i0 ≡c i0
  refli0 t = i0

  postulate
    i0-noloop : (p : i0 ≡c i0) → p ≡c refli0

  retr-case : (i : I) (a : Gel i) (p : i ≡c i0) → gel0 (Gel0≡A-fore-case i a p) ≡c transport (λ t → Gel (p t)) a
  retr-case i (gel {a} r .i) p = (sym (gel0p a r) ) ∙ retr-lemma2 i {g = gel r} p
  retr-case .i0 (gel0 a) p = {!!} -- stuck here, need to use noloop property somehow?
  retr-case .i1 (gel1 b) p = abort p
  retr-case .i0 (gel0p a r i) p = {!!}
  retr-case .i1 (gel1p b r i) p = {!!}

  retr : (a : Gel i0) → gel0 (Gel0≡A-fore-case i0 a (λ _ → i0)) ≡c a
  retr a =  retr-case i0 a (λ _ → i0) ∙ Cubical.Foundations.Prelude.transportRefl a

  Gel0≡A : Gel i0 ≅ A
  Gel0≡A = isoToEquiv (Cubical.Foundations.Isomorphism.iso Gel0≡A-fore gel0 (λ b _ → b) retr)

module functoriality-from-dpush {ℓ  : Agda.Primitive.Level}
            {A B : Set ℓ} (R : A → B → Set ℓ)
            {A' B' : Set ℓ} (R' : A' → B' → Set ℓ)
            {f : A → A'} {g : B → B'}
            (h : {a : A} {b : B} → R a b → R' (f a) (g b))
            (bd : bridge-discrete (sfunc.total R)) where
  open sfunc

  Gel-f : (i : I) → Gel R i → Gel R' i
  Gel-f i  = dpush.pmap R bd (gel0 ∘ f) (gel1 ∘ g) (bgel R' ∘ h) i

  gel-f : {a : A} {b : B} (r : R a b) (i : I) → Gel-f i (gel r i) ≡c gel (h r) i
  gel-f r i t = papp (transp (λ t' → Bridge (Gel R') (gel0p _ (h r) (t' ∧ ~ t)) (gel1p _ (h r) (t' ∧ ~ t))) t (pabs (gel (h r)))) i
