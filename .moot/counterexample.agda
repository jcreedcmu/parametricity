-- with much help from C.B. Aberlé's and Evan Cavallo, cf. fediverse threads at
-- https://mastodon.social/@jcreed/113705418476588154
-- https://mastodon.social/@jcreed/113725334771993306

{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module counterexample where

postulate
  I : Set
  i0 i1 : I

module _ {ℓ : Agda.Primitive.Level} {A B : Set ℓ} (R : A → B → Set ℓ) where
  postulate
    Gel : (i : I) → Set ℓ
    Gel0 : Gel i0 ≡ A
    {-# REWRITE Gel0 #-}
    Gel1 : Gel i1 ≡ B
    {-# REWRITE Gel1 #-}

    -- Gel intro
    gel : {a : A} {b : B} → R a b → (i : I) → Gel i
    gel0 : {a : A} {b : B} (r : R a b) → gel r i0 ≡ a
    {-# REWRITE gel0 #-}
    gel1 : {a : A} {b : B} (r : R a b) → gel r i1 ≡ b
    {-# REWRITE gel1 #-}

    -- Gel elim
    ungel : (g : (i : I) → Gel i) → R (g i0) (g i1)

I-collapse : i0 ≡ i1
I-collapse = ungel _≡_ (λ i → gel _≡_ (refl {x = i}) i)
--                                                ^   ^
--                                    here i is used twice
