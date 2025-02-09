{-# OPTIONS --cubical --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Builtin.Equality  renaming (_≡_ to _≡p_ ; refl to reflp)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Nat hiding (Unit ; _·_)
open import Cubical.Data.Empty renaming (rec to aborti)
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using () renaming (sym to symp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Functions.Embedding
open import Cubical.HITs.Pushout
open import Function.Base
open import Cubical.HITs.S1

module Braids where

data Ival : Set where
 i0 i1 : Ival
 p : i0 ≡ i1

combUnder : {ℓ : Level} {A B : Set ℓ}
       {a1 a2 a3 : A} {a12 : a1 ≡ a2} {a23 : a2 ≡ a3}
       {b1 b2 b3 : B} {b12 : b1 ≡ b2} {b23 : b2 ≡ b3}
       {f : A → B} {f1 : f a1 ≡ b1} {f2 : f a2 ≡ b2} {f3 : f a3 ≡ b3}
     → Square f1 f2 (λ i → f (a12 i)) b12
     → Square f2 f3 (λ i → f (a23 i)) b23
     → Square f1 f3 (λ i → f ((a12 ∙ a23) i)) (b12 ∙ b23)
combUnder = {!!}
infixr 30 combUnder

postulate
 X : Set
 x0 x1 : X
 xp : x0 ≡ x1

 Y : Set
 y0 y1 : Y
 yp : y0 ≡ y1

 f : X → Y
 fp0 : f x0 ≡ y0
 fp1 : f x1 ≡ y1

 fpp : PathP ((λ (i : I) → f (xp i) ≡ yp i)) fp0 fp1

data Unit {ℓ : Level} : Set ℓ where
 ⋆ : Unit

record Cset : Set₁ where constructor mkCset ; field
 Cr : Set
 Bd : S¹ → Cr

_⊗_ : Cset → Cset → Cset
_⊗_ (mkCset Cr1 Bd1) (mkCset Cr2 Bd2) = mkCset carrier boundary where
 carrier : Set
 carrier = Pushout {A = Unit {ℓ-zero}} {B = Cr1} {C = Cr2} (λ _ → Bd1 base) (λ _ → Bd2 base)

 boundary : S¹ → carrier
 boundary base = inl (Bd1 base)
 boundary (loop i) =
    ((λ i → inl (Bd1 (loop i))) ∙ push ⋆ ∙ (λ i → inr (Bd2 (loop i))) ∙ sym (push ⋆)) i

CsetHom : Cset → Cset → Set
CsetHom (mkCset Cr1 Bd1) (mkCset Cr2 Bd2) = Σ[ f ∈ (Cr1 → Cr2) ] ((s : S¹) → f (Bd1 s) ≡ Bd2 s)

⊗functor : {C1 C2 C1' C2' : Cset}
  → CsetHom C1 C2 → CsetHom C1' C2' → CsetHom (C1 ⊗ C1') (C2 ⊗ C2')
⊗functor {C1} {C2} {C1'} {C2'} (f , fp) (g , gp) = gf , gfp where
 gf : Cset.Cr (C1 ⊗ C1') → Cset.Cr (C2 ⊗ C2')
 gf (inl x) = inl (f x)
 gf (inr x) = inr (g x)
 gf (push a i) = lemma i where
  lemma : inl (f (Cset.Bd C1 base)) ≡ inr (g (Cset.Bd C1' base))
  lemma = cong inl (fp base) ∙∙ push ⋆ ∙∙ sym (cong inr (gp base))

 gfp : (s : S¹) → gf (Cset.Bd (C1 ⊗ C1') s) ≡ Cset.Bd (C2 ⊗ C2') s
 gfp base = cong inl (fp base)
 gfp (loop i) = lemma i where
  -- lemma : PathP (λ i → gf (Cset.Bd (C1 ⊗ C1') (loop i)) ≡ Cset.Bd (C2 ⊗ C2') (loop i))
  --               (cong inl (fp base)) (cong inl (fp base))

--  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
-- Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

  lemma1 : PathP (λ i → gf ( inl (Cset.Bd C1 (loop i)))  ≡ ( inl (Cset.Bd C2 (loop i)) ))
                (cong inl (fp base)) (cong inl (fp base))
  lemma1 i j = inl (fp (loop i) j)

  -- lemma2 : PathP (λ i → gf (push ⋆ i) ≡ push ⋆ i)
  --               (cong inl (fp base)) (cong inr (gp base))
  -- lemma2 : Square (cong inl (fp base)) (cong inr (gp base)) (λ i → gf (push ⋆ i)) (push ⋆)

  lemma2 : Square (cong inl (fp base)) (cong inr (gp base)) (cong inl (fp base) ∙∙ push ⋆ ∙∙ sym (cong inr (gp base))) (push ⋆)

  lemma2 i j = doubleCompPath-filler (cong inl (fp base)) (push ⋆) (sym (cong inr (gp base))) (~ j) i

  lemma3 : PathP (λ i → gf ( inr (Cset.Bd C1' (loop i)))  ≡ ( inr (Cset.Bd C2' (loop i)) ))
                (cong inr (gp base)) (cong inr (gp base))
  lemma3 i j = inr (gp (loop i) j)

  -- lemma4 : PathP (λ i → gf (sym (push ⋆) i) ≡ sym (push ⋆) i)
  --               (cong inr (gp base)) (cong inl (fp base))
  lemma4 : Square (cong inr (gp base)) (cong inl (fp base)) (λ i → gf (sym (push ⋆) i)) (sym (push ⋆))

  lemma4 i j = doubleCompPath-filler (cong inl (fp base)) (push ⋆) (sym (cong inr (gp base))) (~ j) (~ i)



  lemma34 :  PathP (λ i → gf (((λ i → inr (Cset.Bd C1' (loop i))) ∙ sym (push ⋆) ) i)
                         ≡ (((λ i → inr (Cset.Bd C2' (loop i))) ∙ sym (push ⋆) ) i))
                (cong inr (gp base)) (cong inl (fp base))
  lemma34 = combUnder {a12 = λ i → inr (Cset.Bd C1' (loop i))}  {a23 = λ i → sym (push ⋆) i} {f = gf} lemma3 lemma4

  lemma234 :  PathP (λ i → gf ((push ⋆ ∙ (λ i → inr (Cset.Bd C1' (loop i))) ∙ sym (push ⋆) ) i)
                         ≡ ((push ⋆ ∙ (λ i → inr (Cset.Bd C2' (loop i))) ∙ sym (push ⋆) ) i))
                (cong inl (fp base)) (cong inl (fp base))
  lemma234 = combUnder {a12 = λ i → push ⋆ i}  {a23 = λ i → ((λ i → inr (Cset.Bd C1' (loop i))) ∙ sym (push ⋆) ) i} {f = gf}
             lemma2 lemma34


  lemma : PathP (λ i → gf (((λ i → inl (Cset.Bd C1 (loop i))) ∙ push ⋆ ∙ (λ i → inr (Cset.Bd C1' (loop i))) ∙ sym (push ⋆)) i)
                         ≡ (((λ i → inl (Cset.Bd C2 (loop i))) ∙ push ⋆ ∙ (λ i → inr (Cset.Bd C2' (loop i))) ∙ sym (push ⋆)) i))
                (cong inl (fp base)) (cong inl (fp base))

  lemma = combUnder {a12 = λ i → inl (Cset.Bd C1 (loop i))}
               {a23 = λ i → (push ⋆ ∙ (λ i → inr (Cset.Bd C1' (loop i))) ∙ sym (push ⋆) ) i}
               {f = gf}
               lemma1 lemma234



-- data Void : Set where


-- abort : (A : Set) → Void → A
-- abort A ()


-- data two : Set where
--  t0 t1 : two

-- data three : Set where
--  c0 c1 c* : three
