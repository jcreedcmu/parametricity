{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality renaming (_≡_ to _≡p_ ; refl to prefl)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

module SST where

postulate
  𝕀 : Set
  * : 𝕀

record SST-gen : Set₁ where
 field
  St : Set
  Z : St → Set
  S : (s : St) (z : Z s) (i : 𝕀) → St
  p : (s : St) (z : Z s) → S s z * ≡p s

module discrete (A : Set) where
  data St : Set where
   dvert : 𝕀 → St

  Z : St → Set
  Z (dvert i) = (i ≡ *) × A

  S : (s : St) (z : Z s) (i : 𝕀) → St
  S s z _ = s -- what does it mean to ignore new i?

  p : (s : St) (z : Z s) → S s z * ≡p s
  p s z = prefl

  discrete : (A : Set) → SST-gen
  discrete A = record { St = St ; Z = Z ; S = S ; p = p }


data SST : Set₁ where
  mks : (Σ[ Z ∈ Set ] (Z → 𝕀 → SST)) → SST

πZ : SST → Set
πZ (mks (Z , S)) = Z

πS : (s : SST) → πZ s → 𝕀 → SST
πS (mks (Z , S)) = S

postulate
  SSTβ : (s : SST) (z : πZ s) → πS s z * ≡p s
  {-# REWRITE SSTβ #-}
