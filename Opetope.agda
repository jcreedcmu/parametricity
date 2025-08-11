module Opetope where

data T₀ : Set where
 Leaf₀ : T₀
 Node₀ : T₀ → T₀

data isUnit₀ : T₀ → Set where
 isUnit₀/ : isUnit₀ (Node₀ Leaf₀)

data locs₀ : T₀ → Set where
 here₀ : (t : T₀) → locs₀ (Node₀ t)
 next₀ : (t : T₀) → locs₀ t → locs₀ (Node₀ t)

data sums₀ : {t : T₀} → (locs₀ t → T₀) → T₀ → Set where

module Containment where
  data T₁ : T₀ → Set where
   Leaf₁ : (t : T₀) → isUnit₀ t → T₁ t
   Node₁ : (t : T₀) (a : locs₀ t → T₀) (k : (p : locs₀ t) → T₁ (a p)) (t' : T₀) → sums₀ a t' → T₁ t'

  data isUnit₁ : {t₀ : T₀} (t₁ : T₁ t₀) → Set where
  data contains₁ : {t₀ : T₀} (t₀' : T₀) (t₁ : T₁ t₀) → Set where
  data sums₁ : {t₀ : T₀} {t₁ : T₁ t₀} (a : (t₀ : T₀) (c : contains₁ t₀ t₁) → T₁ t₀) → T₁ t₀ → Set where


  data T₂ : {t₀ : T₀} (t₁ : T₁ t₀) → Set where
   Leaf₂ : (t₀ : T₀) (t₁ : T₁ t₀) → isUnit₁ t₁ → T₂ t₁
   Node₂ : (t₀ : T₀) (t₁ : T₁ t₀)
           (a : (t₀' : T₀) (c : contains₁ t₀' t₁) → T₁ t₀')
           (k : (t₀' : T₀) (c : contains₁ t₀' t₁) → T₂ (a t₀' c))
           (t₁' : T₁ t₀)
           → sums₁ a t₁'
           → T₂ t₁'

  data isUnit₂ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → Set where
  data contains₂ : {t₀ : T₀} {t₁ : T₁ t₀} {t₀' : T₀} (t₁' : T₁ t₀') (t₂ : T₂ t₁) → Set where
  data sums₂ : {t₀ : T₀} {t₁ : T₁ t₀} {t₂ : T₂ t₁}
      (a : {t₀' : T₀} (t₁' : T₁ t₀') (c : contains₂ t₁' t₂) → T₂ t₁')
      → T₂ t₁ → Set where

  data T₃ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → Set where
   Leaf₃ : (t₀ : T₀) {t₁ : T₁ t₀} (t₂ : T₂ t₁) → isUnit₂ t₂ → T₃ t₂
   Node₃ : (t₀ : T₀) {t₁ : T₁ t₀} (t₂ : T₂ t₁)
           (a : {t₀' : T₀} (t₁' : T₁ t₀') (c : contains₂ t₁' t₂) → T₂ t₁')
           (k : {t₀' : T₀} (t₁' : T₁ t₀') (c : contains₂ t₁' t₂) → T₃ (a t₁' c))
           (t₂' : T₂ t₁)
           → sums₂ a t₂'
           → T₃ t₂'

---- Not strictly positive
--
-- data T : Set
-- isUnit : T → Set
-- contains : T → T → Set

-- data T  where
--  Leaf : (t : T) → isUnit t → T
--  Node₃ : (t : T) →
--          (a : (t' : T) (c : contains t' t) → T)
--          (k : (t' : T) (c : contains t' t) → T)
--          → T

-- isUnit = {!!}
-- contains = {!!}

module Locations where
  data T₁ : T₀ → Set where
   Leaf₁ : (t : T₀) → isUnit₀ t → T₁ t
   Node₁ : (t : T₀) (a : locs₀ t → T₀) (k : (p : locs₀ t) → T₁ (a p)) (t' : T₀) → sums₀ a t' → T₁ t'

  data isUnit₁ : {t₀ : T₀} (t₁ : T₁ t₀) → Set where
  data locs₁ : {t₀ : T₀} (t₁ : T₁ t₀) → Set where
  locBound₁ : {t₀ : T₀} {t₁ : T₁ t₀} (ℓ : locs₁ t₁) → T₀
  locBound₁ ℓ = {!!}

  sum₁ : {t₀ : T₀} {t₁ : T₁ t₀} (a : (ℓ : locs₁ t₁) → T₁ (locBound₁ ℓ)) → T₁ t₀
  sum₁ a = {!!}

  data T₂ : {t₀ : T₀} (t₁ : T₁ t₀) → Set where
   Leaf₂ : (t₀ : T₀) (t₁ : T₁ t₀) → isUnit₁ t₁ → T₂ t₁
   Node₂ : (t₀ : T₀) (t₁ : T₁ t₀)
           (a : (ℓ : locs₁ t₁) → T₁ (locBound₁ ℓ))
           (k : (ℓ : locs₁ t₁) → T₂ (a ℓ))
           → T₂ (sum₁ a)

  data isUnit₂ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → Set where
  data locs₂ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → Set where
  locBound₂₀ : {t₀ : T₀} {t₁ : T₁ t₀} {t₂ : T₂ t₁} (ℓ : locs₂ t₂) → T₀
  locBound₂₀ ℓ = {!!}
  locBound₂ : {t₀ : T₀} {t₁ : T₁ t₀} {t₂ : T₂ t₁} (ℓ : locs₂ t₂) → T₁ (locBound₂₀ ℓ)
  locBound₂ ℓ = {!!}

  sum₂ : {t₀ : T₀} {t₁ : T₁ t₀} {t₂ : T₂ t₁} (a : (ℓ : locs₂ t₂) → T₂ (locBound₂ ℓ)) → T₂ t₁
  sum₂ a = {!!}

  data T₃ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → Set where
   Leaf₃ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁) → isUnit₂ t₂ → T₃ t₂
   Node₃ : {t₀ : T₀} {t₁ : T₁ t₀} (t₂ : T₂ t₁)
           (a : (ℓ : locs₂ t₂) → T₂ (locBound₂ ℓ))
           (k : (ℓ : locs₂ t₂) → T₃ (a ℓ))
           → T₃ (sum₂ a)


data T : Set
isUnit : T → Set
locs : T → Set
∂ : T → T → Set
locBound : {t : T} (ℓ : locs t) → T

data T where
 Leaf : (t : T) → isUnit t → T
 Node : (t : T)
     (a : locs t → T) -- for each location, give a (n-1)-dim tree for what it eventually expands to
     (k : locs t → T) -- for each location, give an n-dim tree for how it expands
     (a' : (ℓ : locs t) → ∂ (a ℓ) (locBound ℓ))
     (k' : (ℓ : locs t) → ∂ (k ℓ) (a ℓ))
     → T

isUnit = {!!}
locs = {!!}
∂ = {!!}
locBound = {!!}
