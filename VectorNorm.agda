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

_n+_ : Num → Num → Num
(x+ , x-) n+ (y+ , y-) = (x+ + y+ , x- + y-)
infixr 10 _n+_

_s×_ : Num → Vec → Vec
s s× (x , y) = (s n× x , s n× y)
infixr 15 _s×_

sqnorm : Vec → Num
sqnorm (x , y) = x n× x n+ y n× y

rotate : Num → Num → Vec → Vec
rotate a b (x , y) = (a n× x n+ b n× y , b n× x n+ a n× y)

_n≡_ : Num → Num → Set
(a+ , a-) n≡ (b+ , b-) = (a+ + b-) ≅ (a- + b+)
infixr 6 _n≡_

thm : (a b : Num) (v : Vec) → sqnorm (rotate a b v) n≡ sqnorm (a , b) n× sqnorm v
thm (a+ , a-) (b+ , b-) ((x+ , x-) , (y+ , y-)) = {!!}
