{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Functions.Embedding
open import Cubical.HITs.Pushout
open import Function.Base

module Balls where

data Void : Set where

abort : (A : Set) → Void → A
abort A ()

data Unit : Set where
 ⋆ : Unit

data two : Set where
 t0 t1 : two

module _ where
 -- Forward declarations for mutual recursion:
 data Tele : Set₁
 record Ball (t : Tele) : Set₁
 BallDom : Tele → Set

 -- Definitions:
 data Tele where
  tnil : Tele
  tcons : (t : Tele) (b1 b2 : Ball t) → Tele
 record Ball t where constructor mkBall ; field
   ⟦_⟧ : Set
   ∂ : BallDom t → ⟦_⟧
 open Ball
 BallDom tnil = Void
 BallDom (tcons t b1 b2) = Pushout (∂ b1) (∂ b2)

data TeleMin : ℕ → Tele → Set₁ where
 tmz : TeleMin zero tnil
 tms : {n : ℕ} (t : Tele) (b1 b2 : Ball t) → TeleMin n t → TeleMin (suc n) (tcons t b1 b2)

module _ where
 open Ball
 Dom1 : {t : Tele} → TeleMin 1 t → Set
 Dom1 (tms _ b _ _) = ⟦ b ⟧
 Cod1 : {t : Tele} → TeleMin 1 t → Set
 Cod1 (tms _ _ b _) = ⟦ b ⟧

 Dom2 : {t : Tele} → TeleMin 2 t → Set
 Dom2 (tms _ _ _ (tms t b _ _)) = ⟦ b ⟧

 Cod2 : {t : Tele} → TeleMin 2 t → Set
 Cod2 (tms _ _ _ (tms t _ b _)) = ⟦ b ⟧

 DomN : {t : Tele} (n : ℕ) → TeleMin (suc n) t → Set
 DomN zero (tms t b1 b2 tm) = ⟦ b1 ⟧
 DomN (suc n) (tms t b1 b2 tm) = DomN n tm

 CodN : {t : Tele} (n : ℕ) → TeleMin (suc n) t → Set
 CodN zero (tms t b1 b2 tm) = ⟦ b2 ⟧
 CodN (suc n) (tms t b1 b2 tm) = CodN n tm

module Hide2 where
 open Ball

 compv : {t : Tele} (A B C : Ball t) → Ball (tcons t A B) → Ball (tcons t B C) → Ball (tcons t A C)
 compv A B C f g = mkBall carrier bd where
  carrier : Set
  carrier = (Pushout (λ (bx : ⟦ B ⟧) → ∂ f (inr bx)) (λ (bx : ⟦ B ⟧) → ∂ g (inl bx)))

  binl : ⟦ f ⟧ → carrier
  binl = inl

  binr : ⟦ g ⟧ → carrier
  binr = inr

  bd : Pushout (∂ A) (∂ C) → carrier
  bd (inl x) = binl (∂ f (inl x))
  bd (inr x) = binr (∂ g (inr x))
  bd (push a i) = lemma i where
   lemma : bd (inl (∂ A a)) ≡ bd (inr (∂ C a))
   lemma = cong (λ q → binl (∂ f q)) (push a) ∙ push (∂ B a) ∙ cong (λ q → binr (∂ g q)) (push a)


 comph : {t₁ t₂ t₃ : Tele}
          → (compo : Ball t₁ → Ball t₂ → Ball t₃)
          → (common : Set) -- between telescopes t₁ and t₂
          → (f h : Ball t₁) (g k : Ball t₂)
          → Ball (tcons t₁ f h) → Ball (tcons t₂ g k) → Ball (tcons t₃ (compo f g) (compo h k))
 comph compo common f h g k α β = mkBall carrier bd where
  carrier : Set
  carrier = {!!}

  bd : Pushout (∂ (compo f g)) (∂ (compo h k)) → carrier
  bd = {!!}
module Hide where
 open Ball

 -- Forward Declarations:

 -- Composable t₁ t₂ t₃ means balls of telescope t₁ and t₂ are composable,
 -- yielding a ball over t₃
 data Composable : Tele → Tele → Tele → Set₁
 -- Actually compute the composite ball
 Compose : {t₁ t₂ t₃ : Tele} (c : Composable t₁ t₂ t₃) → (b₁ : Ball t₁) (b₂ : Ball t₂) → Ball t₃
 -- Now some helpers for composition. Common yields the "common territory" of a composable
 -- pair of telescopes. This is the domain of the two functions that we'll want to push out.
 Common : {t₁ t₂ t₃ : Tele} (c : Composable t₁ t₂ t₃) → Set
 -- Here's how the Common type injects into the "codomain side" of the first map being composed
 CodOf : {t₁ t₂ t₃ : Tele} (c : Composable t₁ t₂ t₃) (b₁ : Ball t₁) → Common c → ⟦ b₁ ⟧
 -- Here's how the Common type injects into the "domain side" of the second map being composed
 DomOf : {t₁ t₂ t₃ : Tele} (c : Composable t₁ t₂ t₃) (b₂ : Ball t₂) → Common c → ⟦ b₂ ⟧
 -- Here's how we construct the boundary injection map
 MkBd : {t₁ t₂ t₃ : Tele} (c : Composable t₁ t₂ t₃) (b₁ : Ball t₁) (b₂ : Ball t₂) (b : BallDom t₃)
     → Pushout (CodOf c b₁) (DomOf c b₂)

 -- Definitions:
 data Composable where
  compz : {t : Tele} (A B C : Ball t) → Composable (tcons t A B) (tcons t B C) (tcons t A C)
  comps : {t₁ t₂ t₃ : Tele}
          (c : Composable t₁ t₂ t₃)
          → (f h : Ball t₁) (g k : Ball t₂)
          → Composable (tcons t₁ f h) (tcons t₂ g k) (tcons t₃ (Compose c f g) (Compose c h k))
 Compose c b₁ b₂ = mkBall (Pushout (CodOf c b₁) (DomOf c b₂)) (MkBd c b₁ b₂)
 Common (compz A B C) = ⟦ B ⟧
 Common (comps c f h g k) = Common c
 CodOf (compz A B C) b₁ xB = ∂ b₁ (inr xB)
 CodOf (comps c f h g k) b₁ xc = ∂ b₁ (inl (CodOf c f xc)) -- asymmetric! why not ∂ b₁ (inr (CodOf c h xc)) ?
 DomOf (compz A B C) b₂ xB = ∂ b₂ (inl xB)
 DomOf (comps c f h g k) b₂ xc = ∂ b₂ (inr (DomOf c k xc)) -- asymmetric! why not ∂ b₂ (inl (DomOf c g xc)) ?
 MkBd (compz A B C) b₁ b₂ (inl xA) = inl (∂ b₁ (inl xA))
 MkBd (compz A B C) b₁ b₂ (inr xC) = inr (∂ b₂ (inr xC))
 MkBd (compz A B C) b₁ b₂ (push a i) = {!!}
 MkBd (comps c f h g k) b₁ b₂ (inl x) = {!x!}
 MkBd (comps c f h g k) b₁ b₂ (inr x) = {!!}
 MkBd (comps c f h g k) b₁ b₂ (push a i) = {!!}

-- For example:
--
-- Ball tnil = { ⟦_⟧ : Set, ∂ : void → ⟦_⟧ }
-- just a set, ideally Unit
--
-- Ball (tcons tnil b1 b2) = { ⟦_⟧ : Set, (b1 .fst + .b2 fst) → ⟦_⟧ }
-- a set with two points

-- This is the canonical 1-point 0-dimensional ball
c0 : Ball tnil
c0 = mkBall Unit (abort Unit)

-- This is the canonical type of 1-dimensional balls
C1 : Set₁
C1 = Ball (tcons tnil c0 c0)


module _ where
 open Ball
 dom : (P : C1) → P .⟦_⟧
 dom P = P .∂ (inl ⋆)

 cod : (P : C1) → P .⟦_⟧
 cod P = P .∂ (inr ⋆)

compose : C1 → C1 → C1
compose p1 p2 = mkBall carrier bound where
   open Ball

   two' : Set
   two' = Pushout (c0 .∂) (c0 .∂) -- pushout of two copies of ! : 0 → 1

   carrier : Set
   carrier = (Pushout (λ (_ : Unit) → cod p1) (λ (_ : Unit) → dom p2))

   bound : two' → carrier
   bound (inl _) = inl (dom p1)
   bound (inr _) = inr (cod p2)

-- To show: compose is associative

-- This is the type of 2-dimensional cells over some boundaries f and g
C2 : C1 → C1 → Set₁
C2 f g = Ball (tcons (tcons tnil c0 c0) f g)

-- Vertical composition of 2-cells
vcompose : {f g h : C1} → C2 f g → C2 g h → C2 f h
vcompose {f} {g} {h} α β = mkBall carrier bound where
 open Ball

 carrier : Set
 carrier = Pushout (α .∂ ∘ inr) (β .∂ ∘ inl)

 cinl : ⟦ α ⟧ → carrier
 cinl = inl

 cinr : ⟦ β ⟧ → carrier
 cinr = inr

 two' : Set
 two' = Pushout (c0 .∂) (c0 .∂)

 boundLemma : (a : two') → cinl (α .∂ (inl (f .∂ a))) ≡ cinr (β .∂ (inr (h .∂ a)))
 boundLemma a = cong (λ q → cinl (α .∂ q)) (push a)
              ∙ push (g .∂ a)
              ∙ cong (λ q → cinr (β .∂ q)) (push a)

 bound : Pushout (f .∂) (h .∂) → carrier
 bound (inl fx) = inl (α .∂ (inl fx))
 bound (inr hx) = inr (β .∂ (inr hx))
 bound (push a i) = boundLemma a i

-- horizontal composition of 2-cells
hcompose : {f g h k : C1} → C2 f g → C2 h k → C2 (compose f h) (compose g k)
hcompose {f} {g} {h} {k} α β = mkBall carrier {!bound!} where
 carrier : Set
 carrier = Pushout {!!} {!!}
