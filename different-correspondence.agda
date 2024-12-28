-- with much help from C.B. Aberlé's and Evan Cavallo, cf. fediverse threads at
-- https://mastodon.social/@jcreed/113705418476588154
-- https://mastodon.social/@jcreed/113725334771993306

{-# OPTIONS --cubical --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Function.Base

module different-correspondence where

-- a little equality lemma without importing the whole lib

ap : ∀ {ℓ} {A B : Set ℓ} {a a' : A} (f : A → B) → a ≡ a' → f a ≡ f a'
ap f refl = refl

-- The interval

postulate
  I : Set
  i0 i1 : I

-- Convenience type for maps 𝕀 → A with specified endpoints

module _ {ℓ : Agda.Primitive.Level} (A : I → Set ℓ) where
  postulate
    Bridge : A i0 → A i1 → Set ℓ

module _ {ℓ : Agda.Primitive.Level} {A : I → Set ℓ} where
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

-- below we assert that this is a left and right inverse of K : A → (I → A)
-- as pdβ and pdη, not the most elegant way of doing it, but eh.
bridge-discrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
bridge-discrete A = (I → A) → A

bridge-discrete-rel : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set ℓ) → Set ℓ
bridge-discrete-rel {A = A} {B} R = {a : A} {b : B} → bridge-discrete (R a b)

module _ {ℓ : Agda.Primitive.Level} {A B : I → Set ℓ} (R : {i : I} → A i → B i → Set ℓ) where
  postulate
    Gel : (i : I) → Set ℓ
    Gel0 : Gel i0 ≡ A i0
    {-# REWRITE Gel0 #-}
    Gel1 : Gel i1 ≡ B i1
    {-# REWRITE Gel1 #-}

    -- Here we assert that, for any {a : (i : I) → (A i)} {b : (i : I) → (B i)}
    -- that there is an equivalence of
    -- (r : (i : I) → R (a i) (b i))
    -- and
    -- Bridge Gel (a i0) (b i1)
    gel' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
         (r : (i : I) → R (a i) (b i))
         → Bridge Gel (a i0) (b i1)
    ungel' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
         → Bridge Gel (a i0) (b i1) → ((i : I) → R (a i) (b i))

  postulate
    Gelβ' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
          (r : (i : I) → R (a i) (b i)) → ungel' (gel' r) ≡ r
    {-# REWRITE Gelβ' #-}
    Gelη' : {a : (i : I) → (A i)} {b : (i : I) → (B i)}
          (g : Bridge Gel (a i0) (b i1)) → gel' (ungel' {a} {b} g) ≡ g
    {-# REWRITE Gelη' #-}

-- Now we investigate how this assumption reduces in the non-dependent case
module _ {ℓ : Agda.Primitive.Level} {A B : Set ℓ} (R : A → B → Set ℓ) where

  -- We can define Gel intro
  gel : {a : A} {b : B} → R a b → (i : I) → Gel R i
  gel r i = papp (gel' R (λ _ → r)) i
  gel0 : {a : A} {b : B} (r : R a b) → gel r i0 ≡ a
  gel0 r = refl
  gel1 : {a : A} {b : B} (r : R a b) → gel r i1 ≡ b
  gel1 r = refl

  -- But defining the elim rule, and establishing β and η, requires
  -- assuming that R is bridge discrete.

  module _ (pdr : bridge-discrete-rel R) where
    postulate
      pdβ : {a : A} {b : B} (r : R a b) → pdr (λ _ → r) ≡ r
      pdη : {a : A} {b : B} (f : (i : I) → R a b) → (λ _ → pdr f) ≡ f

    -- Gel elim
    ungel : {a : A} {b : B} →  Bridge (Gel R) a b → R a b
    ungel = pdr ∘ (ungel' R)

    -- Gel properties
    Gelβ : {a : A} {b : B} (r : R a b) → ungel (pabs (gel r)) ≡ r
    Gelβ r = pdβ r

    Gelη : {a : A} {b : B} (p : Bridge (Gel R) a b) (i : I) → gel (ungel p) i ≡ papp p i
    Gelη p i = ap (λ z → papp ((gel' R) z) i) (pdη (ungel' R p))
