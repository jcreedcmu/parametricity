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

module foo where

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

  coΩfunctor : {a : A} {b : B} (k : (i : I) → Ω R i → Ω R' i) (r : R a b) → R' (k i0 a) (k i1 b)
  coΩfunctor k r = α R' (pabs λ i → k i (ω R r i))

module paramNat (F : (X : Set) → X → (X → X) → X)
                (A B : Set) (R : A → B → Set)
                (a : A) (b : B) (r : R a b)
                (f : A → A) (g : B → B)
                (h : (a : A) (b : B) → R a b → R (f a) (g b))
                where
  param : R (F A a f) (F B b g)
  param = α R (pabs λ i → F (Ω R i) (ω R r i) (Ωfunctor R R h i))



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
