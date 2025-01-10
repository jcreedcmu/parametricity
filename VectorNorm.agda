{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (_⊎_ to _+_)
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

module VectorNorm where

Num : Set₁
Num = Set × Set

Vec : Set₁
Vec = Num × Num

_n×_ : Num → Num → Num
(x+ , x-) n× (y+ , y-) = (x+ × y+ + x- × y- , x+ × y- + x- × y+)
infixr 15 _n×_

neg : Num → Num
neg (x+ , x-) = (x- , x+)

_n+_ : Num → Num → Num
(x+ , x-) n+ (y+ , y-) = (x+ + y+ , x- + y-)
infixr 10 _n+_

_s×_ : Num → Vec → Vec
s s× (x , y) = (s n× x , s n× y)
infixr 15 _s×_

sqnorm : Vec → Num
sqnorm (x , y) = x n× x n+ y n× y

rotate : Vec → Vec → Vec
rotate (a , b) (x , y) = (a n× x n+ b n× y , neg b n× x n+ a n× y)

_n≡_ : Num → Num → Set
(a+ , a-) n≡ (b+ , b-) = (a+ + b-) ≅ (a- + b+)
infixr 6 _n≡_

module _ (a+ a- b+ b- x+ x- y+ y- : Set) where
 a : Num
 a = (a+ , a-)
 x : Num
 x = (x+ , x-)
 b : Num
 b = (b+ , b-)
 y : Num
 y = (y+ , y-)

-- (ax + by)² + (-bx + ay)² = (a² + b²)(x² + y²)
-- a²x² + b²y² + b²x² + a²y²
 lemma3 :
    (a n× x n+ b n× y) n× (a n× x n+ b n× y) n+
    (neg b n× x n+ a n× y) n× (neg b n× x n+ a n× y)
  n≡ (a n× a n+ b n× b) n× (x n× x n+ y n× y)
 lemma3 = isoToEquiv (iso {!fore!} {!!} {!!} {!!}) where
    fore : fst
      ((a n× x n+ b n× y) n× (a n× x n+ b n× y) n+
       (neg b n× x n+ a n× y) n× (neg b n× x n+ a n× y))
      + snd ((a n× a n+ b n× b) n× (x n× x n+ y n× y)) →
      snd
      ((a n× x n+ b n× y) n× (a n× x n+ b n× y) n+
       (neg b n× x n+ a n× y) n× (neg b n× x n+ a n× y))
      + fst ((a n× a n+ b n× b) n× (x n× x n+ y n× y))
    fore (inl (inl x₁)) = {!!}
    fore (inl (inr x₁)) = {!!}
    fore (inr x₁) = {!!}

 lemma2 :
     sqnorm (a n× x n+ b n× y , neg b n× x n+ a n× y)
  n≡ sqnorm (a , b) n× sqnorm (x , y)
 lemma2 = lemma3

lemma : (a+ a- b+ b- x+ x- y+ y- : Set) →
    sqnorm (rotate ((a+ , a-), (b+ , b-))  ((x+ , x-), (y+ , y-)))
 n≡ sqnorm ((a+ , a-), (b+ , b-)) n× sqnorm ((x+ , x-), (y+ , y-))
lemma = lemma2

thm : (w v : Vec) → sqnorm (rotate w v) n≡ sqnorm w n× sqnorm v
thm ((a+ , a-), (b+ , b-)) ((x+ , x-) , (y+ , y-)) = lemma a+ a- b+ b- x+ x- y+ y-
