module Opetope2 where
open import Agda.Primitive

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

module _ (C₀ : Set) where

 S₁ = C₀ → C₀ → Set

 module _ {C₁ : S₁} where
  data T₀ : S₁ where
   Leaf₀ : (c : C₀) → T₀ c c
   Node₀ : {a b c : C₀} (kids : T₀ b c) (first : C₁ a b) → T₀ a c

 module _ (C₁ : S₁) where

  record B₂ : Set where
   constructor mkB₂
   field
    {c} {c'} : C₀
    f : C₁ c c'
    f' : T₀ {C₁} c c'

  S₂ = B₂ → Set

  η : {c c' : C₀} → C₁ c c' → T₀ {C₁} c c'
  η = {!!}

  module _ {C₂ : S₂} where
   data T₁ : S₂ where
    Leaf₁ : (c c' : C₀) (f : C₁ c c') → T₁ (mkB₂ f (η f))
    Node₁ : (c c' : C₀) (f : C₁ c c') (kids : T₀ {C₁ = λ c c' → Σ[ f ∈ C₁ c c' ] Σ[ f' ∈ T₀ c c' ] T₁ (mkB₂ f f')} c c') → T₁ (mkB₂ f {!!})
