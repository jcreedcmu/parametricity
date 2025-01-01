{-# OPTIONS --cubical --rewriting #-}

module 1labe-experiment where

open import Function.Base
open import Cubical.Relation.Nullary.Base using (¬_)
open import Agda.Builtin.Cubical.Equiv using (isEquiv ; equivFun )
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive using (Level)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv using (funIsEq ; invIsEq ; retIsEq ; secIsEq ; compEquiv ; invEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Prelude renaming (_≡_ to _≡c_ ; i0 to ci0 ; i1 to ci1 ; I to cI)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Agda.Builtin.Cubical.Equiv using () renaming (_≃_ to _≅_)

data ⊤ {ℓ : Level}: Set ℓ where
  * : ⊤

Σ-⊤-triv : ∀ {ℓ} {B : ⊤ {ℓ} → Type ℓ} → (Σ ⊤ B) ≅ B *
Σ-⊤-triv {B = B}  =
  isoToEquiv (iso (λ { (* , b) → b }) (λ b → (* , b)) (λ b _ → b) λ { (* , b) _ → (* , b) })

Σ-contr-⊤ : ∀ {ℓ} {A : Type ℓ} → isContr A → A ≡c ⊤
Σ-contr-⊤ {A = A}  (center , paths) =
  ua (isoToEquiv (iso (λ _ → *) (λ _ → center) (λ { * u → * }) paths))


Σ-contr-eqv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (c : isContr A)
  → (Σ A B) ≅ B (c .fst)
Σ-contr-eqv = {!ua!}

Σ-contr-eqv2 : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ}
  → (c : isContr A)
  → (Σ A B) ≅ B (c .fst)
Σ-contr-eqv2 {ℓ} {A = A} c = (transport (λ t → map (goal (~ t))) Σ-⊤-triv) where
  discard : (y : ⊤ {ℓ}) → * ≡c y
  discard * _ = *

  A-bundle : Σ[ Z ∈ Set ℓ ] isContr Z
  A-bundle = A , c
  ⊤-bundle : Σ[ Z ∈ Set ℓ ] isContr Z
  ⊤-bundle = ⊤ , * , discard

  typeq : A ≡c ⊤
  typeq = Σ-contr-⊤ c

  center-path : PathP (λ t → typeq t) (fst c) *
  center-path u = transp (λ t → sym typeq (t ∧ ~ u)) u *

  paths-path : PathP (λ t → (y : typeq t) → center-path t ≡c y) (snd c) discard
  paths-path    = {!!}

  goal : A-bundle ≡c ⊤-bundle
  goal u = (Σ-contr-⊤ c u , center-path u , paths-path u)

  map : (Σ[ Z ∈ Set ℓ ] isContr Z) → Set (ℓ-suc ℓ)
  map (Z , (c , π)) = {B : Z → Set ℓ} → Σ Z B ≅ B c

isProp∙→isContr : ∀ {ℓ} {A : Type ℓ} → isProp A → A → isContr A
isProp∙→isContr prop x .fst = x
isProp∙→isContr prop x .snd y = prop x y

_e⁻¹ : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : Type ℓ₁}
     → (A ≅ B) → (B ≅ A)
_e⁻¹ = invEquiv

_e∙_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
     → A ≅ B → B ≅ C → A ≅ C
_e∙_ = compEquiv

infixr 30 _e∙_
infix 31 _e⁻¹

module propLem2 {ℓ k : Level} (E : Set ℓ) (A B : E → Set k) (E-isProp : isProp E) (sumeq : (Σ[ e ∈ E ] A e) ≅ (Σ[ e ∈ E ] B e)) where

  lemma2 : (Σ[ e ∈ E ] A e) ≡c (Σ[ e ∈ E ] B e) → (e : E) → A e ≡c B e
  lemma2 h e = {!!}

  lemma : (Σ[ e ∈ E ] A e) ≅ (Σ[ e ∈ E ] B e) → (e : E) → A e ≅ B e
  lemma h e = (Σ-contr-eqv (isProp∙→isContr E-isProp e) e⁻¹)
                    e∙ h
                    e∙ Σ-contr-eqv (isProp∙→isContr E-isProp e)
