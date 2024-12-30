{-# OPTIONS --cubical --rewriting #-}

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Cubical.Foundations.Prelude using (sym ; _∙_ ; isContr ; transport ; transportRefl ; transp ; ~_ ; _∧_ ; _∨_ ) renaming (_≡_ to _≡c_ ; i0 to ci0)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

module injection where

-- The interval

module _ (X : Set) where -- X is the shape of the interval, e.g. 2 for binary relations
  postulate
    I : Set
    ι : X → I -- endpoints of the interval

  -- Equalities in X become equalities in I...
  ι-cong : {x y : X} (p : x ≡c y) → ι x ≡c ι y
  ι-cong p i = ι (p i)

  -- ...and we assert these are the only equalities in I between
  -- elements of X injected into I. ι-conj is an embedding.
  postulate
    ι-cong-equiv : (x y : X) → isEquiv (ι-cong {x} {y})

  module _ {ℓ : Level} (A : I → Set ℓ) where
    postulate
      -- Convenience type for maps (i : I) → A i with specified endpoints
      Bridge : ((x : X) → A (ι x)) → Set ℓ

  module _ {ℓ : Level} {A : I → Set ℓ} where
    postulate
      pabs : (f : (i : I) → A i) → Bridge A (f ∘ ι)
      papp : {a : (x : X) → A (ι x)} → Bridge A a → (i : I) → A i
      pβ : (f : (i : I) → A i) (i : I) → papp (pabs f) i ≡ f i
      {-# REWRITE pβ #-}
      pβι : {a : (x : X) → A (ι x)} (p : Bridge A a) (x : X) → papp p (ι x) ≡ a x
      {-# REWRITE pβι #-}
      pη : {a : (x : X) → A (ι x)} (p : Bridge A a) → pabs (λ i → papp p i) ≡ p
      {-# REWRITE pη #-}

  -- A type is bridge discrete if the constant combinator A → I → A is
  -- an equivalence
  bridge-discrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  bridge-discrete A = isEquiv λ (a : A) (i : I) → a

  -- The typical meaning of A changes here, from an I-indexed to an X-indexed type family.
  -- R is a relation, a type family indexed by global elements of A.
  module pushout {ℓ : Level} {A : X → Set ℓ} (R : ((x : X) → A x) → Set ℓ) where

    -- the total space of the relation R, so that we can assert it is
    -- bridge-discrete with respect to the interval of interest.

    record total : Set ℓ where
     field
      ge : (x : X) → A x -- global element of A
      rh : R ge -- the relation holds of that element

    -- Instead of postulating the Gel type, we define it as a pushout,
    -- and effectively postulate that "ungel" works, for path-discrete
    -- relations.

    data Gel : (i : I) → Set ℓ where
      -- One component of the pushout is R × I, where the 'connective tissue' of the relation lives
      gel : {a : (x : X) → A x} (r : R a) (i : I) → Gel i
      -- The second component is (x : X) × A x, where the endpoints live
      gelι : {x : X} (ax : A x) → Gel (ι x)
      -- And we assert that inℓ (r, i) ≡ inr (x, aₓ) when i ≡ ι x and aₓ = πₓ r,
      -- i.e. i is the actual endpoing in I corresponding to x,
      -- and aₓ is the projection of r to the x'th arm of the relation
      gelιp : (x : X) (a : (x : X) → A x) (r : R a)  → gel r (ι x) ≡c gelι (a x)

    -- gel, but make a bridge
    bgel : {a : (x : X) → A x} (r : R a) → Bridge Gel (gelι ∘ a)
    bgel {a} r = transport (λ t → Bridge Gel λ x → gelιp x a r t) (pabs (gel r))

    module _ (bd : bridge-discrete total) where

      -- This is where we assert the existence of ungel. The imagined
      -- model is a presheaf model of reflexive graphs with X-shaped
      -- endpoints. If the total space of the relation is bridge
      -- discrete, then any global element of the pushout should have
      -- come from one specific a.
      --
      -- This seems plausible to me because colimits are computed
      -- object-wise in presheaf categories.
      postulate
        bgel-isEquiv : {a : (x : X) → A x} → isEquiv (bgel {a})

      ungel : {a : (x : X) → A x} → Bridge Gel (gelι ∘ a) → R a
      ungel p = invIsEq bgel-isEquiv p

      Gelβ : {a : (x : X) → A x} (r : R a) → ungel (bgel r) ≡ r
      Gelβ r = pathToEq (retIsEq bgel-isEquiv r)

      Gelη : {a : (x : X) → A x} (p : Bridge Gel (gelι ∘ a)) (i : I) → bgel (ungel p) ≡ p
      Gelη p i = pathToEq (secIsEq bgel-isEquiv p)

    extract-lemma : {x y : X} (a : (x : X) → A x) (p : y ≡c x) →
              transport (λ t → A (p t)) (a y) ≡c a x
    extract-lemma a p u = transp (λ t → A (p (t ∨ u))) u (a (p u))

    extract' : (x : X) (i : I) → Gel i → (i ≡c ι x) → A x
    extract' x i (gel {a} r .i) p = a x
    extract' x .(ι _) (gelι {y} ay) p = transport (λ t → A (invIsEq (ι-cong-equiv y x) p t)) ay
    extract' x .(ι y) (gelιp y a r u) p = extract-lemma a (λ t → invIsEq (ι-cong-equiv y x) p t) (~ u)

    extract : {x : X} → Gel (ι x) → A x
    extract {x} g = extract' x (ι x) g (λ _ → ι x)

    section-lemma : (x : X) → invIsEq (ι-cong-equiv x x) (λ _ → ι x) ≡c (λ _ → x)
    section-lemma x = (λ t → invIsEq (ι-cong-equiv x x) (λ _ → ι x)) ∙ retIsEq (ι-cong-equiv x x) (λ _ → x)

    section : (x : X) (ax : A x) → extract (gelι ax) ≡c ax
    section x ax = (λ u → transport (λ t → A (section-lemma x u t)) ax) ∙ transportRefl ax

    retract2 : (x : X) (i : I) (g : Gel i) (p : i ≡c ι x) → gelι (extract' x i g p) ≡c transport (λ t → Gel (p t)) g
    retract2 x a = {!!}

    retract : (x : X) (g : Gel (ι x)) → gelι (extract g) ≡c g
    retract x g = retract2 x (ι x) g (λ _ → ι x) ∙ transportRefl g

    Gel-endpoints : (x : X) → Gel (ι x) ≅ A x
    Gel-endpoints x = isoToEquiv (Cubical.Foundations.Isomorphism.iso extract gelι (section x) (retract x))
  --   retract : (a : Gel i0) → gel0 (fore i0 a (λ _ → i0)) ≡c a
  --   retract a = retract' i0 a (λ _ → i0) ∙ Cubical.Foundations.Prelude.transportRefl a

  --   Gel0≡A' : Gel i0 ≅ A
  --   Gel0≡A' = isoToEquiv (Cubical.Foundations.Isomorphism.iso fore' gel0 cvtA/ retract)


  --   abort : (p : i1 ≡c i0) {A : Set ℓ} → A
  --   abort p {A} = Cubical.Data.Empty.elim {A = λ _ → A} (Bridge-nontriv p)


  --   Gel0≡A-fore-case : (i : I) → Gel i → i ≡c i0 → A
  --   Gel0≡A-fore-case .i (gel {a} r i) p = a
  --   Gel0≡A-fore-case .i0 (gel0 a) p = a
  --   Gel0≡A-fore-case .i1 (gel1 b) p = abort p
  --   Gel0≡A-fore-case .i0 (gel0p a r i) p = a
  --   Gel0≡A-fore-case .i1 (gel1p {a} b r i) p = abort p {a ≡c abort p} i

  --   Gel0≡A-fore : Gel i0 → A
  --   Gel0≡A-fore g = Gel0≡A-fore-case i0 g (λ _ → i0)

  --   retr-lemma2 : (i : I) {G : I → Set ℓ} {g : (i : I) → G i} (p : i ≡c i0) →  g i0 ≡c transport (λ t → G (p t)) (g i)
  --   retr-lemma2 = {!!}

  --   refli0 : i0 ≡c i0
  --   refli0 t = i0

  --   postulate
  --     i0-noloop : (p : i0 ≡c i0) → p ≡c refli0

  --   retr-case : (i : I) (a : Gel i) (p : i ≡c i0) → gel0 (Gel0≡A-fore-case i a p) ≡c transport (λ t → Gel (p t)) a
  --   retr-case i (gel {a} r .i) p = (sym (gel0p a r) ) ∙ retr-lemma2 i {g = gel r} p
  --   retr-case .i0 (gel0 a) p = {!!} -- stuck here, need to use noloop property somehow?
  --   retr-case .i1 (gel1 b) p = abort p
  --   retr-case .i0 (gel0p a r i) p = {!!}
  --   retr-case .i1 (gel1p b r i) p = {!!}

  --   retr : (a : Gel i0) → gel0 (Gel0≡A-fore-case i0 a (λ _ → i0)) ≡c a
  --   retr a =  retr-case i0 a (λ _ → i0) ∙ Cubical.Foundations.Prelude.transportRefl a

  --   Gel0≡A : Gel i0 ≅ A
  --   Gel0≡A = isoToEquiv (Cubical.Foundations.Isomorphism.iso Gel0≡A-fore gel0 (λ b _ → b) retr)

  -- module functoriality-from-dpush {ℓ  : Agda.Primitive.Level}
  --             {A B : Set ℓ} (R : A → B → Set ℓ)
  --             {A' B' : Set ℓ} (R' : A' → B' → Set ℓ)
  --             {f : A → A'} {g : B → B'}
  --             (h : {a : A} {b : B} → R a b → R' (f a) (g b))
  --             (bd : bridge-discrete (sfunc.total R)) where
  --   open sfunc

  --   Gel-f : (i : I) → Gel R i → Gel R' i
  --   Gel-f i  = dpush.pmap R bd (gel0 ∘ f) (gel1 ∘ g) (bgel R' ∘ h) i

  --   gel-f : {a : A} {b : B} (r : R a b) (i : I) → Gel-f i (gel r i) ≡c gel (h r) i
  --   gel-f r i t = papp (transp (λ t' → Bridge (Gel R') (gel0p _ (h r) (t' ∧ ~ t)) (gel1p _ (h r) (t' ∧ ~ t))) t (pabs (gel (h r)))) i
