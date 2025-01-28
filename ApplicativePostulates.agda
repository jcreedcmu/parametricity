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
   ℓ ℓ' ℓ'' : Level

postulate
 F : Type ℓ → Type ℓ
 G : F (Type ℓ) → Type ℓ
 η : {A : Type ℓ} → A → F A



postulate
 ⟪_,_⟫F : {A : Type ℓ} {B : Type ℓ'} → F A → F B → F (A × B)
 _·_ : {A : Type ℓ} {B : Type ℓ'} → F (A → B) → F A → F B
 ⟪_,_⟫dF : {A : Type ℓ} {B : A → Type ℓ'} → (a : F A) → G (η B · a) → F (Σ A B)
 _·d_ : {A : Type ℓ} {B : A → Type ℓ'} (f : F ((x : A) → B x)) (x : F A) → G (η B · x)


module _ {A : Type ℓ} {B : Type ℓ'} where
 fmap : (A → B) → F A → F B
 fmap f x = η f · x

postulate
 -- η·β2 needed for ΣF and ΠF to typecheck
 --
 -- I don't love how specialized this is to the particular pair
 -- arguments, but I can't think of a better consequence of
 -- applicative axioms that reduce directionally in a nice way.
 η·β1 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (a : A) (fb : F B) (g : A × B → C) → η g · ⟪ η a , fb ⟫F ≡p fmap (λ b → g (a , b)) fb
 η·β2 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (fa : F A) (b : B) (g : A × B → C) → η g · ⟪ fa , η b ⟫F ≡p fmap (λ a → g (a , b)) fa
 {-# REWRITE η·β1 #-}
 {-# REWRITE η·β2 #-}



Fsub : {A : Type ℓ} (B : A → Type ℓ') (M : F A) → F (Type ℓ')
Fsub B M = η B · M

_×F_ : (A : F (Type ℓ)) (B : F (Type ℓ')) → F (Type (ℓ ⊔ ℓ'))
A ×F B = Fsub (λ x → (x .fst) × (x .snd)) ⟪ A , B ⟫F

_→F_ : (A : F (Type ℓ)) (B : F (Type ℓ')) → F (Type (ℓ ⊔ ℓ'))
A →F B = Fsub (λ x → (x .fst) → (x .snd)) ⟪ A , B ⟫F

ΣF : (A : F (Type ℓ)) (B : G(A →F η (Type ℓ'))) → F (Type (ℓ ⊔ ℓ'))
ΣF {ℓ} {ℓ'} A B = Fsub (λ x → Σ (x .fst) (x .snd)) (⟪_,_⟫dF A B)

ΠF : (A : F (Type ℓ)) (B : G(A →F η (Type ℓ'))) → F (Type (ℓ ⊔ ℓ'))
ΠF {ℓ} {ℓ'} A B = Fsub (λ x → (y : x .fst) → x .snd y) (⟪_,_⟫dF A B)

postulate
 GηF : {A : Type ℓ} → G (η A) ≡p F A
 {-# REWRITE GηF #-}

 η·η : {A : Type ℓ} (f : A → Type ℓ') (a : A) → G (η f · η a) ≡p F (f a)
 {-# REWRITE η·η #-}

postulate
 ⟪_,_⟫G : {A : F (Type ℓ)} {B : F (Type ℓ')} (M : G A) (N : G B) → G (A ×F B)
 _·G_ : {A : F (Type ℓ)} {B : F (Type ℓ')} (M : G (A →F B)) (N : G A) → G B
 ⟪_,_⟫dG : {A : F (Type ℓ)} {B : G(A →F η (Type ℓ'))} (M : G A) (N : G (_·G_ {A = A} {B = η (Type ℓ')} B M)) → G (ΣF A B)
 _·dG_ : {A : F (Type ℓ)} {B : G(A →F η (Type ℓ'))} (M : G (ΠF A B)) (N : G A) → G (_·G_ {A = A} {B = η (Type ℓ')} B N)

module _ {A : Type ℓ} {B : A → Type ℓ'} where
 dfst : F (Σ A B) → F A
 dfst = fmap fst

 dmap : ((x : A) → B x) → (a : F A) → G (η B · a)
 dmap f x = η f ·d x

 dsnd : (M : F (Σ A B)) → G (η (B ∘ fst) · M)
 dsnd M = η snd ·d M
