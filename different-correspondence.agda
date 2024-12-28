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

module different-correspondence where

postulate
  I : Set
  i0 i1 : I

module _ {ℓ : Agda.Primitive.Level} (A : I → Set ℓ) where
  postulate
    Path : A i0 → A i1 → Set ℓ

ap : ∀ {ℓ} {A B : Set ℓ} {a a' : A} (f : A → B) → a ≡ a' → f a ≡ f a'
ap f refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl p = p

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
    {-# REWRITE pη #-}


-- below we assert that this is a left and right inverse of K : A → (I → A)
-- as pdβ and pdη, not the most elegant way of doing it, but eh.
path-discrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
path-discrete A = (I → A) → A

path-discrete-rel : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set ℓ) → Set ℓ
path-discrete-rel {A = A} {B} R = {a : A} {b : B} → path-discrete (R a b)

module _ {ℓ : Agda.Primitive.Level} {A B : I → Set ℓ} (R : {i : I} → A i → B i → Set ℓ) where
  postulate
    Ω : (i : I) → Set ℓ
    Ω0 : Ω i0 ≡ A i0
    {-# REWRITE Ω0 #-}
    Ω1 : Ω i1 ≡ B i1
    {-# REWRITE Ω1 #-}

    ω' : {a : (i : I) → (A i)} {b : (i : I) → (B i)} (r : (i : I) → R (a i) (b i))
         → Path Ω (a i0) (b i1)
    α' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
         → Path Ω (a i0) (b i1) → ((i : I) → R (a i) (b i))

  postulate
    Ωβ' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
          (r : (i : I) → R (a i) (b i)) → α' (ω' r) ≡ r
    {-# REWRITE Ωβ' #-}
    Ωη' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
          (g : Path Ω (a i0) (b i1)) → ω' (α' {a} {b} g) ≡ g
    {-# REWRITE Ωη' #-}

-- degenerate down to non-dependent relations
module _ {ℓ : Agda.Primitive.Level} {A B : Set ℓ} (R : A → B → Set ℓ) where

  -- Ω intro
  ω : {a : A} {b : B} → R a b → (i : I) → Ω R i
  ω r i = papp (ω' R (λ _ → r)) i
  ω0 : {a : A} {b : B} (r : R a b) → ω r i0 ≡ a
  ω0 r = refl
  ω1 : {a : A} {b : B} (r : R a b) → ω r i1 ≡ b
  ω1 r = refl

  module _ (pdr : path-discrete-rel R) where
    postulate
      pdβ : {a : A} {b : B} (r : R a b) → pdr (λ _ → r) ≡ r
      pdη : {a : A} {b : B} (f : (i : I) → R a b) → (λ _ → pdr f) ≡ f

    -- Ω elim
    α : {a : A} {b : B} →  Path (Ω R) a b → R a b
    α = pdr ∘ (α' R)

    -- Ω properties
    Ωβ : {a : A} {b : B} (r : R a b) → α (pabs (ω r)) ≡ r
    Ωβ r = pdβ r

    Ωη : {a : A} {b : B} (p : Path (Ω R) a b) (i : I) → ω (α p) i ≡ papp p i
    Ωη p i = ap (λ z → papp ((ω' R) z) i) (pdη (α' R p))
