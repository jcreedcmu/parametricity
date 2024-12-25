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

module foo-generalized where

postulate
  ● : (X : Set) → Set
  at : {X : Set} → X → ● X

module _ {ℓ : Agda.Primitive.Level} {X : Set} (A : ● X → Set ℓ) where
  postulate
    Path : ((x : X) → A (at x)) → Set ℓ

module _ {ℓ : Agda.Primitive.Level} {X : Set} {A : ● X → Set ℓ} where
  postulate
    pabs : (f : (i : ● X) → A i) → Path A (f ∘ at)
    papp : {a : (x : X) → A (at x)} → Path A a → (i : ● X) → A i
    pβ : (f : (i : ● X) → A i) (i : ● X) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    pβat : {a : (x : X) → A (at x)} (p : Path A a) (t : X) → papp p (at t) ≡ a t
    {-# REWRITE pβat #-}
    pη : {a : (x : X) → A (at x)} (p : Path A a) → pabs (papp p) ≡ p
    {-# REWRITE pη #-}

module _ {ℓ : Agda.Primitive.Level} {X : Set} {A : X → Set ℓ} (R : ((x : X) → A x) → Set ℓ) where
  postulate
    Ω : (i : ● X) → Set ℓ
    Ωat : (x : X) → Ω (at x) ≡ A x
    {-# REWRITE Ωat #-}

    -- Ω intro
    ω : {a : (x : X) → A x} → R a → (i : ● X) → Ω i
    ωat : {a : (x : X) → A x} (r : R a) (x : X) → ω r (at x) ≡ a x
    {-# REWRITE ωat #-}

    -- Ω elim
    α : {a : (x : X) → A x} → Path Ω a → R a
    Ωβ : {a : (x : X) → A x} (r : R a) → α (pabs (ω r)) ≡ r
    {-# REWRITE Ωβ #-}
    Ωη : {a : (x : X) → A x} (p : Path Ω a) (i : ● X) → ω (α p) i ≡ papp p i
    {-# REWRITE Ωη #-}

-- module _ {ℓ k : Agda.Primitive.Level}
--          {A B : Set ℓ} (R : A → B → Set ℓ)
--          {A' B' : Set k} (R' : A' → B' → Set k)
--          {f : A → A'} {g : B → B'}
--          (h : (a : A) (b : B) → R a b → R' (f a) (g b)) where
--   postulate
--     Ωfunctor : (i : I) → Ω R i → Ω R' i
--     ωfunctor : {a : A} {b : B} (r : R a b) (i : I) → Ωfunctor i (ω R r i) ≡ ω R' (h a b r) i
--     {-# REWRITE ωfunctor #-}
--     ωfunctor0 : (a : A) → Ωfunctor i0 a ≡ f a
--     {-# REWRITE ωfunctor0 #-}
--     ωfunctor1 : (b : B) → Ωfunctor i1 b ≡ g b
--     {-# REWRITE ωfunctor1 #-}

--   coΩfunctor : {a : A} {b : B} (k : (i : I) → Ω R i → Ω R' i) (r : R a b) → R' (k i0 a) (k i1 b)
--   coΩfunctor k r = α R' (pabs λ i → k i (ω R r i))

-- module paramNat (F : (X : Set) → X → (X → X) → X)
--                 (A B : Set) (R : A → B → Set)
--                 (a : A) (b : B) (r : R a b)
--                 (f : A → A) (g : B → B)
--                 (h : (a : A) (b : B) → R a b → R (f a) (g b))
--                 where
--   param : R (F A a f) (F B b g)
--   param = α R (pabs λ i → F (Ω R i) (ω R r i) (Ωfunctor R R h i))



-- module paramPhoas (F : (X : Set) → ((X → X) → X) → X)
--                 (A B : Set) (R : A → B → Set)
--                 (f : (A → A) → A) (g : (B → B) → B)
--                 (f~g : (f' : A → A) (g' : B → B)
--                        (f'~g' : (a : A) (b : B) → R a b → R (f' a) (g' b)) → R (f f') (g g'))
--                 where

--   gg : Path (Ω R) (F A f) (F B g)
--   gg = {!!}

--   param : R (F A f) (F B g)
--   param = α R gg
