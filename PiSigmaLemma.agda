{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Function.Base

Π : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Π A B = (x : A) → B x

module hide {ℓ ℓ' : Level} (A : Set ℓ) (B : A → Set ℓ') where
  fore : Π A B → (Σ[ f ∈ (A → Σ A B) ] ((a : A) → f a .fst ≡ a))
  fore f = (λ a → a , (f a)) , (λ a → refl)

  back : (Σ[ f ∈ (A → Σ A B) ] ((a : A) → f a .fst ≡ a)) → Π A B
  back (f , q) a = subst B (q a) (f a .snd)

  sect : (s : Σ[ f ∈ (A → Σ A B) ] ((a : A) → f a .fst ≡ a)) → fore (back s) ≡ s
  sect (f , q) i = (λ a → (q a (~ i)) ,
                           transp (λ j → B (q a (j ∧ ~ i))) i (f a .snd)) ,
                           λ a j → q a (j ∨ ~ i)

  retr : (f : Π A B) → back (fore f) ≡ f
  retr f i x = transportRefl (f x) i

  ΠΣ-lemma : Π A B ≅ (Σ[ f ∈ (A → Σ A B) ] ((a : A) → f a .fst ≡ a))
  ΠΣ-lemma = isoToEquiv (iso fore back sect retr)

lemma = hide.ΠΣ-lemma
