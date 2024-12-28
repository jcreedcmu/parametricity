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

module _ {ℓ : Agda.Primitive.Level} (A : I → Set ℓ) where
  postulate
    Bridge : A i0 → A i1 → Set ℓ

module _ {ℓ : Agda.Primitive.Level} {A : I → Set ℓ} where
  postulate
    pabs : (f : (i : I) → A i) → Bridge A (f i0) (f i1)
    papp : {a0 : A i0} {a1 : A i1} → Bridge A a0 a1 → (i : I) → A i

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
    ungel : {a : A} {b : B} → Bridge Gel a b → R a b

I-surprise : (R : I → I → Set) (R-refl : (i : I) → R i i) → R i0 i1
I-surprise R R-refl = ungel R (pabs λ i → gel R (R-refl i) i)

I-collapse : i0 ≡ i1
I-collapse = I-surprise _≡_ (λ _ → refl)
