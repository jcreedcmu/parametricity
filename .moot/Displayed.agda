{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Equiv  renaming (_≃_ to _≅_)
open import Agda.Primitive
open import Cubical.Data.Equality.Conversion using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

module Displayed where

postulate
 T : Set
 * : T

record Graph : Set₁ where
 field
  Vert : Set
  Edge : (v w : Vert) → Set
open Graph

record TGraph : Set₁ where
 field
  TVert : T → Set
  TEdge : (t : T) → (v w : TVert t) → Set
open TGraph

record DGraph (G : Graph) : Set₁ where
 field
  DVert : G .Vert → Set
  DEdge : {v w : G .Vert} → DVert v → DVert w → G .Edge v w → Set
open DGraph

thm1 : TGraph ≅ (T → Graph)
thm1  = isoToEquiv (iso fore back sect retr) where
 fore : TGraph → T → Graph
 fore record { TVert = TVert ; TEdge = TEdge } t =
      record { Vert = TVert t ; Edge = λ v w → TEdge t v w }

 back : (T → Graph) → TGraph
 back f =
      record { TVert = λ t → f t .Vert ; TEdge = λ t v w → f t .Edge v w }

 sect : (g : T → Graph) → fore (back g) ≡ g
 sect g i = g

 retr : (g : TGraph) → back (fore g) ≡ g
 retr g i = g

thm2 : (G : Graph) → DGraph G ≅ Σ TGraph (λ f → equivFun thm1 f * ≡ G)
thm2 G = isoToEquiv (iso {!!} {!!} {!!} {!!}) where
  back : Σ TGraph (λ f → equivFun thm1 f * ≡ G) → DGraph G
  back (record { TVert = TVert ; TEdge = TEdge } , compat) =
        record { DVert = {!!} ; DEdge = {!!} }

thm : (G : Graph) → DGraph G ≅ (Σ[ f ∈ (T → Graph) ] f * ≡ G)
thm G = compEquiv (thm2 G) ((Σ-cong-equiv-fst {A = TGraph} {A' = T → Graph}  {B = λ f → f * ≡ G}  thm1))
