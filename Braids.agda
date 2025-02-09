{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1

module Braids where

data Unit {ℓ : Level} : Set ℓ where
 ⋆ : Unit

-- a Cset is a set with a specified circle in it
record Cset : Set₁ where constructor mkCset ; field
 -- The carrier set:
 Cr : Set
 -- The boundary:
 Bd : S¹ → Cr

{-
 These have a tensor product.

 - The carrier of the tensor product of Csets A and B is a pushout of
   the carriers of A and B, with one path connecting the basepoints of
   the boundaries of A and B.

 - The basepoint of the tensor product's boundary is chosen to be the
   basepoint of A.

 - The loop of the tensor product's boundary starts at base_A, does
   one loop around A, traverses the pushout path to base_B, does a
   loop around B, and traverses the pushout path back to base_A.

  loop_A      loop_B
   ┌──>──┐   ┌──>──┐
   │     │   │     │
   ^  A  v   ^  B  v
   │     │ > │     │
   └──<──*─<─*──<──┘

        /     \
  base_A       base_B
-}
_⊗_ : Cset → Cset → Cset
_⊗_ (mkCset Cr1 Bd1) (mkCset Cr2 Bd2) = mkCset carrier boundary where
 carrier : Set
 carrier = Pushout {A = Unit {ℓ-zero}} {B = Cr1} {C = Cr2} (λ _ → Bd1 base) (λ _ → Bd2 base)

 boundary : S¹ → carrier
 boundary base = inl (Bd1 base)
 boundary (loop i) =
    ((λ i → inl (Bd1 (loop i))) ∙ push ⋆ ∙ (λ i → inr (Bd2 (loop i))) ∙ sym (push ⋆)) i

infixr 30 _⊗_

{- A homomorphism between Csets is a function of their carriers that preserves the boundary. -}
CsetHom : Cset → Cset → Set
CsetHom (mkCset Cr1 Bd1) (mkCset Cr2 Bd2) = Σ[ f ∈ (Cr1 → Cr2) ] ((s : S¹) → f (Bd1 s) ≡ Bd2 s)

{- Conjecture: With internalized parametricity, the following type is contractible -}
BraidsOverOneStrand : Set₁
BraidsOverOneStrand = (C : Cset) → CsetHom C C

{- Conjecture: With internalized parametricity, the following type is isomorphic to ℤ. -}
BraidsOverTwoStrands : Set₁
BraidsOverTwoStrands = (C : Cset) → CsetHom (C ⊗ C) (C ⊗ C)

{- Conjecture: With internalized parametricity, the following type is isomorphic to the braid group B₃. -}
BraidsOverThreeStrands : Set₁
BraidsOverThreeStrands = (C : Cset) → CsetHom (C ⊗ C ⊗ C) (C ⊗ C ⊗ C)

{- etc. -}
