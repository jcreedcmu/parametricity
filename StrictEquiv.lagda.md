---
title: Strictly Involutive Equivalence
---

<!--
```agda
{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_ ; pathToEquiv to p2e)
open import Agda.Builtin.Equality using () renaming (_≡_ to _≡p_)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module StrictEquiv where

infix 4 _≅'_
```
-->

An alternative notion of equivalence, bootstrapped off of an existing one.
We merely give ourselves one type's worth of "slack", to make the definition
more symmetric.

```agda
record _≅'_ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set (ℓ-suc ℓ) where
 field
  R : Set ℓ
  f : R → A
  g : R → B
  fe : isEquiv f
  ge : isEquiv g
```

<blockquote>
Parenthetically: A bummer about this definition is it's at level ℓ+1
rather than ℓ. Is there any way we can keep it at level ℓ by
interpreting it as a codata type? It smells something like a type of
lazy pairs enhanced by equivalence information.

    codata _&_ (A : Set ℓ) (B : Set ℓ) : Set ℓ where
      π₁ : A & B → A
      π₂ : A & B → B
      γ₁ : (a : A) → isContr (fiber π₁ a)
      γ₂ : (b : B) → isContr (fiber π₂ b)

Except the two γ clauses are illegal,
because they're not out of the type A & B.
</blockquote>

 Anyway.
 First we compute all the usual things that we can compute from an equivalence
```agda
module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅' B) where
 open _≅'_ q
 ff = funIsEq fe
 fg = funIsEq ge
 if = invIsEq fe
 ig = invIsEq ge

 getFun : A → B
 getFun = fg ∘ if

 getInv : B → A
 getInv = ff ∘ ig

 getSec : (b : B) → getFun (getInv b) ≡ b
 getSec b = cong fg (retIsEq fe (ig b)) ∙ secIsEq ge b

 getRet : (a : A) → getInv (getFun a) ≡ a
 getRet a = cong ff (retIsEq ge (if a)) ∙ secIsEq fe a

 invert : B ≅' A
 invert = record { R = R ; f = g ; g = f ; fe = ge ; ge = fe }

```
 Inversion is strictly involutive, and all of the useful properties
 are strictly exchanged under inversion as expected
```agda
module _ {ℓ : Level} {A B : Set ℓ} (q : A ≅' B) where
 open _≅'_

 invert-strict-inv : invert (invert q) ≡ q
 invert-strict-inv = refl

 invertPresFun : getFun q ≡ getInv (invert q)
 invertPresFun = refl

 invertPresInv : getInv q ≡ getFun (invert q)
 invertPresInv = refl

 invertPresRet : getRet q ≡ getSec (invert q)
 invertPresRet = refl

 invertPresSec : getSec q ≡ getRet (invert q)
 invertPresSec = refl
```

 The reflexivity equivalence is also preserved under inversion:

```agda
module _ {ℓ : Level} {A : Set ℓ} where
 reflEquiv : A ≅' A
 reflEquiv = record { R = A ; f = λ x → x ; g = λ x → x ;
                      fe = idIsEquiv A ; ge = idIsEquiv A }

 invertRefl : invert (reflEquiv) ≡ reflEquiv
 invertRefl = refl
```
