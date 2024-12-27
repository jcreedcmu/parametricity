-- this is almost entirely C.B. Aberlé's code, from here:
-- https://mastodon.social/@jcreed/113705418476588154
-- I massaged it only slightly to use more modules for argument brevity
-- The point of copying it here is so that I can ask the question:
--
-- Is the fact that I seem stuck proving paramPhoas.param due
-- to me going about the proof the wrong way, or is it
-- a real obstacle?

{-# OPTIONS --cubical --rewriting #-}
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Core.Primitives
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Function.Base

module foo-suspicious-axiom where

postulate
  I : Set
  i0 i1 : I

module _ {ℓ : Agda.Primitive.Level} (A : I → Set ℓ) where
  postulate
    Path : A i0 → A i1 → Set ℓ

module _ {ℓ : Agda.Primitive.Level} {A : I → Set ℓ} where
  postulate
    pabs : (f : (i : I) → A i) → Path A (f i0) (f i1)
    papp : {a0 : A i0} {a1 : A i1} → Path A a0 a1 → (i : I) → A i
    pβ : (f : (i : I) → A i) (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    pβ0 : {a0 : A i0} {a1 : A i1} (p : Path A a0 a1) → papp p i0 ≡ a0
    {-# REWRITE pβ0 #-}
    pβ1 : {a0 : A i0} {a1 : A i1} (p : Path A a0 a1) → papp p i1 ≡ a1
    {-# REWRITE pβ1 #-}
    pη : {a0 : A i0} {a1 : A i1} (p : Path A a0 a1) → pabs (λ i → papp p i) ≡ p

module _ {ℓ : Agda.Primitive.Level} {A B : Set ℓ} (R : A → B → Set ℓ) where
  postulate
    Ω : (i : I) → Set ℓ
    Ω0 : Ω i0 ≡ A
    {-# REWRITE Ω0 #-}
    Ω1 : Ω i1 ≡ B
    {-# REWRITE Ω1 #-}

    -- Ω intro
    ω : {a : A} {b : B} → R a b → (i : I) → Ω i
    ω0 : {a : A} {b : B} (r : R a b) → ω r i0 ≡ a
    {-# REWRITE ω0 #-}
    ω1 : {a : A} {b : B} (r : R a b) → ω r i1 ≡ b
    {-# REWRITE ω1 #-}

    -- Ω elim
    α : {a : A} {b : B} → Path Ω a b → R a b
    Ωβ : {a : A} {b : B} (r : R a b) → α (pabs (ω r)) ≡ r
    {-# REWRITE Ωβ #-}
    Ωη : {a : A} {b : B} (p : Path Ω a b) (i : I) → ω (α p) i ≡ papp p i
    {-# REWRITE Ωη #-}

-- This is where I try implementing a version of ecavallo's "extent"
-- primitive; it is called coextent here for I forget what reason

ap : ∀ {ℓ} {A B : Set ℓ} {a a' : A} (f : A → B) → a ≡ a' → f a ≡ f a'
ap f refl = refl

module _ {ℓ : Agda.Primitive.Level} {V : I → Set ℓ} {W : I → Set ℓ}
       where
  extent : {f : V i0 → W i0} {g : V i1 → W i1}
        → (h : Path (λ i → V i → W i) f g)
        → (v : (i : I) → V i) → Path W (f (v i0)) (g (v i1))
  extent h v = pabs λ i → papp h i (v i)

  postulate
    coextent : (f : V i0 → W i0) (g : V i1 → W i1)
            → ((v : (i : I) → V i) → Path W (f (v i0)) (g (v i1)))
            → Path (λ i → V i → W i) f g
    extentβ : (f : V i0 → W i0) (g : V i1 → W i1)
              → (vv : (v : (i : I) → V i) → Path W (f (v i0)) (g (v i1)))
              → extent (coextent f g vv) ≡ vv

  extentβ' : (f : V i0 → W i0) (g : V i1 → W i1)
          → (vv : (v' : (i : I) → V i) → Path W (f (v' i0)) (g (v' i1)))
          → (v : (i : I) → V i)
          → (i : I)
          → papp (coextent f g vv) i (v i) ≡ papp (vv v) i
  extentβ' f g vv v i = ap (λ x → papp (x v) i) (extentβ f g vv)

-- Here I'm trying to think of Ω as being a certain pushout

module push {ℓ : Agda.Primitive.Level} {A B Q : Set ℓ} (R : A → B → Set ℓ)
         (qa : A → Q) (qb : B → Q) (qf : {a : A} {b : B} (r : R a b) (i : I) → Q)
         (qae : (a : A) (b : B) (r : R a b) → qa a ≡ qf r i0)
         (qbe : (a : A) (b : B) (r : R a b) → qb b ≡ qf r i1)
         where
  postulate
    pmap : (i : I) → Ω R i → Q
    p0 : pmap i0 ≡ qa
    p1 : pmap i1 ≡ qb
    pf : (a : A) (b : B) (r : R a b) (i : I) → pmap i (ω R r i) ≡ qf r i

-- Here I'm trying to think of Ω as being... a dependent pushout??

module dpush {ℓ : Agda.Primitive.Level} {A B : Set ℓ} {Q : I → Set ℓ} (R : A → B → Set ℓ)
         (qa : A → Q i0) (qb : B → Q i1) (qf : {a : A} {b : B} (r : R a b) (i : I) → Q i)
         (qae : (a : A) (b : B) (r : R a b) → qa a ≡ qf r i0)
         (qbe : (a : A) (b : B) (r : R a b) → qb b ≡ qf r i1)
         where
  postulate
    pmap : (i : I) → Ω R i → Q i
    p0 : pmap i0 ≡ qa
    p1 : pmap i1 ≡ qb
    pf : (a : A) (b : B) (r : R a b) (i : I) → pmap i (ω R r i) ≡ qf r i
    -- missing: uniqueness of the induced map. probably related to various η principles

-- dependent pushout implies Ωfunctor

module Ωfunctor-from-dpush {ℓ  : Agda.Primitive.Level}
            {A B : Set ℓ} (R : A → B → Set ℓ)
            {A' B' : Set ℓ} (R' : A' → B' → Set ℓ)
            {f : A → A'} {g : B → B'}
            (h : {a : A} {b : B} → R a b → R' (f a) (g b)) where
  Ωf : (i : I) → Ω R i → Ω R' i
  Ωf i  = dpush.pmap {Q = Ω R'} R f g (ω R' ∘ h) (λ _ _ _ → refl) (λ _ _ _ → refl) i

-- coextent and extentβ imply Ωfunctor and ωfunctor

fixup : ∀ {ℓ} {Q : I → Set ℓ} {x0 y0 : Q i0} {x1 y1 : Q i1} (e0 : y0 ≡ x0) (e1 : y1 ≡ x1)
    → Path Q x0 x1
    → Path Q y0 y1
fixup refl refl p = p


module dpush-from-coextent {ℓ : Agda.Primitive.Level} {A B : Set ℓ} {Q : I → Set ℓ} (R : A → B → Set ℓ)
         (qa : A → Q i0) (qb : B → Q i1) (qf : {a : A} {b : B} (r : R a b) (i : I) → Q i)
         (qae : (a : A) (b : B) (r : R a b) → qa a ≡ qf r i0)
         (qbe : (a : A) (b : B) (r : R a b) → qb b ≡ qf r i1)
         where

  pmap : (i : I) → Ω R i → Q i
  pmap i = papp (coextent qa qb λ v → fixup (qae (v i0) (v i1) (α R (pabs v)))
                                             (qbe (v i0) (v i1) (α R (pabs v)))
                                             (pabs (qf (α R (pabs v))))) i
  p0 : pmap i0 ≡ qa
  p0 = refl
  p1 : pmap i1 ≡ qb
  p1 = refl

  pf' : (a : A) (b : B) (r : R a b) (i : I) → pmap i (ω R r i) ≡
         papp ((fixup (qae ((ω R r) i0) ((ω R r) i1) (α R (pabs (ω R r))))
                      (qbe ((ω R r) i0) ((ω R r) i1) (α R (pabs (ω R r))))
                      (pabs (qf r))) ) i
  pf' a b r i = extentβ' qa qb (λ v → fixup (qae (v i0) (v i1) (α R (pabs v))) (qbe (v i0) (v i1) (α R (pabs v))) (pabs (qf (α R (pabs v))))) (ω R r) i

  -- stuck?
  pf : (a : A) (b : B) (r : R a b) (i : I) → pmap i (ω R r i) ≡ qf r i
  pf a b r i = {!!}


-- coextent and extentβ imply Ωfunctor and ωfunctor

module Ωfunctor-from-coextent {ℓ  : Agda.Primitive.Level}
         {A B : Set ℓ} (R : A → B → Set ℓ)
         {A' B' : Set ℓ} (R' : A' → B' → Set ℓ)
         {f : A → A'} {g : B → B'}
         (h : (a : A) (b : B) → R a b → R' (f a) (g b)) where
  Ωf : (i : I) → Ω R i → Ω R' i
  Ωf i  = papp (coextent f g λ v → pabs (ω R' (h (v i0) (v i1) (α R (pabs v))))) i

  ωf : {a : A} {b : B} (r : R a b) (i : I) → Ωf i (ω R r i) ≡ ω R' (h a b r) i
  ωf r i = extentβ' f g (λ v → pabs (ω R' (h (v i0) (v i1) (α R (pabs v))))) (ω R r) i

-- vestigial postulating of Ωfunctor and ωfunctor, so
-- I can use rewriting

module _ {ℓ k : Agda.Primitive.Level}
         {A B : Set ℓ} (R : A → B → Set ℓ)
         {A' B' : Set k} (R' : A' → B' → Set k)
         {f : A → A'} {g : B → B'}
         (h : (a : A) (b : B) → R a b → R' (f a) (g b)) where
  postulate
    Ωfunctor : (i : I) → Ω R i → Ω R' i
    ωfunctor : {a : A} {b : B} (r : R a b) (i : I) → Ωfunctor i (ω R r i) ≡ ω R' (h a b r) i
    {-# REWRITE ωfunctor #-}
    ωfunctor0 : (a : A) → Ωfunctor i0 a ≡ f a
    {-# REWRITE ωfunctor0 #-}
    ωfunctor1 : (b : B) → Ωfunctor i1 b ≡ g b
    {-# REWRITE ωfunctor1 #-}

-- Thinking about η principle that corresponds to Ωfunctor's role
-- as a β principle

module _ {ℓ k : Agda.Primitive.Level}
         {A B : Set ℓ} (R : A → B → Set ℓ)
         {A' B' : Set k} (R' : A' → B' → Set k)
         where
  α2 : {f : A → A'} {g : B → B'} (p : Path (λ i → Ω R i → Ω R' i) f g) → (a : A) (b : B) (r : R a b) → (R' (f a) (g b))
  α2 p a b r = α R' (pabs λ i → papp p i (ω R r i))

  ω2 : {f : A → A'} {g : B → B'} (h : (a : A) (b : B) (r : R a b) → (R' (f a) (g b))) → (i : I) → Ω R i → Ω R' i
  ω2 h = Ωfunctor R R' h

  Ωβ2 : {f : A → A'} {g : B → B'} (h : (a : A) (b : B) (r : R a b) → (R' (f a) (g b))) → α2 (pabs (ω2 h)) ≡ h
  Ωβ2 h = refl -- this is true by ωfunctor and Ωβ reductions

  -- postulate?
  Ωη2 : {f : A → A'} {g : B → B'} (p : Path (λ i → Ω R i → Ω R' i) f g) (i : I) → ω2 (α2 p) i ≡ papp p i
  Ωη2 = {!!}

  coΩfunctor : (j : (i : I) → Ω R i → Ω R' i) → ((a : A) (b : B) → (r : R a b) → R' (j i0 a) (j i1 b))
  coΩfunctor j a b r = α R' (pabs λ i → j i (ω R r i))

  cof-f : (f : A → A') (g : B → B')
          (h : (a : A) (b : B) → R a b → R' (f a) (g b))
          (a : A) (b : B) (r : R a b)
          → coΩfunctor (Ωfunctor R R' h) a b r ≡ h a b r
  cof-f f g h a b r = refl -- this is true by ωfunctor and Ωβ reductions

  f-cof : (j : (i : I) → Ω R i → Ω R' i) (i : I)
          → Ωfunctor R R' (coΩfunctor j) i ≡ j i
  f-cof j = Ωη2 (pabs j)

-- Parametricity for church nats

module paramNat (F : (X : Set) → X → (X → X) → X)
                (A B : Set) (R : A → B → Set)
                (a : A) (b : B) (r : R a b)
                (f : A → A) (g : B → B)
                (h : (a : A) (b : B) → R a b → R (f a) (g b))
                where
  param : R (F A a f) (F B b g)
  param = α R (pabs λ i → F (Ω R i) (ω R r i) (Ωfunctor R R h i))

-- Parametricity for a phoas-like type, not sure
-- how to prove

module paramPhoas (F : (X : Set) → ((X → X) → X) → X)
                (A B : Set) (R : A → B → Set)
                (f : (A → A) → A) (g : (B → B) → B)
                (f~g : (f' : A → A) (g' : B → B)
                       (f'~g' : (a : A) (b : B) → R a b → R (f' a) (g' b)) → R (f f') (g g'))
                where

  gg : Path (Ω R) (F A f) (F B g)
  gg = {!!}

  param : R (F A f) (F B g)
  param = α R gg
