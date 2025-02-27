-- substantial debt owed to C.B. Aberlé's code, from here:
-- https://mastodon.social/@jcreed/113705418476588154
-- and ensuing conversation with @ecavallo

{-# OPTIONS --cubical --rewriting #-}
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Core.Primitives
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Function.Base

module ecavallo-convo where

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
    pβ : (f : (i : I) → A i) (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    pβ0 : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → papp p i0 ≡ a0
    {-# REWRITE pβ0 #-}
    pβ1 : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → papp p i1 ≡ a1
    {-# REWRITE pβ1 #-}
    pη : {a0 : A i0} {a1 : A i1} (p : Bridge A a0 a1) → pabs (λ i → papp p i) ≡ p
    {-# REWRITE pη #-}

module _ {ℓ : Agda.Primitive.Level} {A B : Set ℓ} (R : A → B → Set ℓ) where
  postulate
    Ω : (i : I) → Set ℓ
    Ω0 : Ω i0 ≡ A
    {-# REWRITE Ω0 #-}
    Ω1 : Ω i1 ≡ B
    {-# REWRITE Ω1 #-}

module _ {ℓ : Agda.Primitive.Level} {V : I → Set ℓ}  {W : I → Set ℓ}
         {f : V i0 → W i0} {g : V i1 → W i1}
       where
  alter : (h : Bridge (λ i → V i → W i) f g)
        → (v : (i : I) → V i) → Bridge W (f (v i0)) (g (v i1))
  alter h v = pabs λ i → papp h i (v i)

  postulate
    invAlter :  (b : (v : (i : I) → V i) → Bridge W (f (v i0)) (g (v i1)))
        → Bridge (λ i → V i → W i) f g

    alter-zig : (b : (v : (i : I) → V i) → Bridge W (f (v i0)) (g (v i1))) → alter (invAlter b) ≡ b
    alter-zag : (h : Bridge (λ i → V i → W i) f g) → invAlter (alter h) ≡ h

module _ {ℓ : Agda.Primitive.Level} {U : Set ℓ} {W : I → Set ℓ} {f : U → W i0} {g : U → W i1} where

  alter' : (h : Bridge (λ i → U → W i) f g)
         → (v : U) → Bridge W (f v) (g v)
  alter' h v = alter h (λ _ → v)

  invAlter' :  (b : (v : U) → Bridge W (f v) (g v))
                  → Bridge (λ i → U → W i) f g
  invAlter' b =  pabs λ i v → papp (b v) i

module _ {ℓ : Agda.Primitive.Level} {U : Set ℓ} {W : I → Set ℓ} {f : U → W i0} {g : U → W i1} where

  alter'-zig :  (b : (v : U) → Bridge W (f v) (g v)) (v : U) → alter' (invAlter' b) v ≡ b v
  alter'-zig b v = refl

  -- I can get this close
  lemma2 : (h : Bridge (λ i → U → W i) f g) →
          (λ (i : I) (v : U) → papp (pabs λ i → papp h i v) i)
        ≡ (λ (i : I) (v : U) → papp h i v)
  lemma2 h = refl

  lemma : (h : Bridge (λ i → U → W i) f g) →
          (pabs λ (i : I) (v : U) → papp (pabs λ i → papp h i v) i)
        ≡ (pabs λ (i : I) (v : U) → papp h i v)
  lemma h = {!!} -- ...but I can't get here

  alter'-zag : (h : Bridge (λ i → U → W i) f g) → invAlter' (alter' h) ≡ h
  alter'-zag h = lemma h

module _ (A : Set) where
  Pb : Bridge (λ i → Set) A A
  Pb = pabs λ i → Ω {A = A} (λ a a' → a ≡ a') i

  P : I → Set
  P i = papp Pb i

  foo : Bridge (λ i → A → P i) (λ x → x) (λ x → x)
        → (v : I → A) → Bridge P (v i0) (v i1)
  foo = alter
