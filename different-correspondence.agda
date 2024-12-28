-- with much help from C.B. Aberlé's and Evan Cavallo, cf. fediverse threads at
-- https://mastodon.social/@jcreed/113705418476588154
-- https://mastodon.social/@jcreed/113725334771993306

{-# OPTIONS --cubical --rewriting #-}
open import Cubical.Core.Primitives renaming (_≡_ to _≡c_) hiding (I ; i0 ; i1)
open import Agda.Builtin.Cubical.Equiv using (isEquiv)
open import Cubical.Foundations.Isomorphism using (isoToIsEquiv)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Function.Base
import Cubical.Foundations.Prelude
open import Cubical.Data.Equality.Conversion using (eqToPath ; pathToEq)

module different-correspondence where

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

-- A type is bridge discrete if the constant combinator A → I → A is
-- an equivalence
bridge-discrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
bridge-discrete A = isEquiv λ (a : A) (i : I) → a

-- A relation is bridge discrete if for every a, b the type R a b is.
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

    -- This is a little more dependent than I'm used to seeing, but
    -- maybe has already been studied?
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
    -- Gel elim
    ungel : {a : A} {b : B} →  Bridge (Gel R) a b → R a b
    ungel b = invIsEq pdr (ungel' R b)

    -- Gel properties
    Gelβ : {a : A} {b : B} (r : R a b) → ungel (pabs (gel r)) ≡ r
    Gelβ r = pathToEq (retIsEq pdr r)

    Gelη : {a : A} {b : B} (p : Bridge (Gel R) a b) (i : I) → gel (ungel p) i ≡ papp p i
    Gelη p i = pathToEq (λ t → papp (gel' R (secIsEq pdr (ungel' R p) t)) i)
