{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Interval.Axioms
open import Interval.Discreteness
import Interval.Gel
import Interval.Functoriality
open import Function.Base

module ApplicativePostulates where

module _ where
 variable
   ℓ ℓ' : Level

postulate
 F : Type ℓ → Type ℓ
 Fd' : (ℓ : Level) → F (Type ℓ) → Type ℓ
 η : {A : Type ℓ} → A → F A

Fd : {ℓ : Level} → F (Type ℓ) → Type ℓ
Fd {ℓ}  = Fd' ℓ

postulate
 ⟪_,_⟫F : {A : Type ℓ} {B : Type ℓ'} → F A → F B → F (A × B)
 _·_ : {A : Type ℓ} {B : Type ℓ'} → F (A → B) → F A → F B
 d⟪_,_⟫F : {A : Type ℓ} {B : A → Type ℓ'} → (a : F A) → Fd (η B · a) → F (Σ A B)
 _·d_ : {A : Type ℓ} {B : A → Type ℓ'} (f : F ((x : A) → B x)) (x : F A) → Fd (η B · x)

Fsub : {A : Type ℓ} (B : A → Type ℓ') (M : F A) → F (Type ℓ')
Fsub B M = η B · M

_×F_ : (A B : F (Type ℓ)) → F (Type ℓ)
A ×F B = Fsub (λ x → (x .fst) × (x .snd)) ⟪ A , B ⟫F

_→F_ : (A : F (Type ℓ)) (B : F (Type ℓ')) → F (Type (ℓ ⊔ ℓ'))
A →F B = Fsub (λ x → (x .fst) → (x .snd)) ⟪ A , B ⟫F

ΣF : (A : F (Type ℓ)) (B : Fd(A →F η (Type ℓ'))) → F (Type (ℓ ⊔ ℓ'))
ΣF {ℓ} {ℓ'} A B = Fsub (λ x → Σ {a = ℓ} {b = ℓ'} (x .fst) (x .snd)) (d⟪_,_⟫F A {!Fd (η (λ v → v → Type ℓ') · A)!})

-- need : Fd' (ℓ-max ℓ (ℓ-suc ℓ')) (η (λ v → v → Type ℓ') · A)
--    B : Fd' (ℓ-max ℓ (ℓ-suc ℓ')) (η (λ x → x .fst → x .snd) · ⟪ A , η (Type ℓ') ⟫F)

-- postulate
--  GηF : {A : Type ℓ} → Fd (η A) ≡p F A
--  {-# REWRITE GηF #-}

--  η·η : {A : Type ℓ} (f : A → Type ℓ') (a : A) → Fd (η f · η a) ≡p F (f a)
--  {-# REWRITE η·η #-}

-- module _ {A : Type ℓ} {B : Type ℓ'} where
--  fmap : (A → B) → F A → F B
--  fmap f x = η f · x

-- module _ {A : Type ℓ} {B : A → Type ℓ'} where
--  dfst : F (Σ A B) → F A
--  dfst = fmap fst

--  dmap : ((x : A) → B x) → (a : F A) → Fd (η B · a)
--  dmap f x = η f ·d x

--  dsnd : (M : F (Σ A B)) → Fd (η (B ∘ fst) · M)
--  dsnd M = η snd ·d M
