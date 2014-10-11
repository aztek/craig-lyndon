module CraigLyndon where

open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Vec hiding (_∈_)

open import Subset
open import Subset.Properties
open import Formula
open import Formula.Properties

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Data.Empty
open import Data.Fin
open import Data.Fin.Props

CraigLyndon : ∀ {n} (A B : Formula n) → Set
CraigLyndon A B = ⊨ A ⇒ B → ∃ λ C → (atoms C ⊆ atoms A ∩ atoms B) ⋀ (⊨ A ⇒ C) ⋀ (⊨ C ⇒ B)

data Δ-Atoms {n} (A B : Formula n) : Set where
  [] : Empty (atoms A − atoms B) → Δ-Atoms A B
  _⟨_⟩∷_ : ∀ x → x ∈ (atoms A − atoms B) → Δ-Atoms (A ∸ x) B → Δ-Atoms A B

Δ-atoms : ∀ {n} (A B : Formula n) → Δ-Atoms A B
Δ-atoms A B = helper A B (induction (atoms A − atoms B))
  where helper : ∀ A B → Induction (atoms A − atoms B) → Δ-Atoms A B
        helper A B ([] ∉) = [] ∉
        helper A B (_∷_ {x} x∈∸ i) = x ⟨ x∈∸ ⟩∷ helper (A ∸ x) B {!!}

interpolate : ∀ {n} (A B : Formula n) → CraigLyndon A B
interpolate A B = Δ-induction A B (Δ-atoms _ _)
  where
    Δ-induction : ∀ A B → Δ-Atoms A B → CraigLyndon A B
    Δ-induction A B ([] ∉) ⊨A⇒B = A , A⊆A∩B , ⊨A⇒A , ⊨A⇒B
      where
        A⊆A∩B = ⊆-intersection ∉
        ⊨A⇒A  = tautology A
    Δ-induction A B (x ⟨ x∈Δ ⟩∷ i) ⊨A⇒B
      with Δ-induction (A ∸ x) B i (⊨A∸x⇒B A B x ⊨A⇒B)
    ...  | C , C⊆A∸x∩B , ⊨A∸x⇒C , ⊨C⇒B = C , C⊆A∩B , ⊨A⇒C , ⊨C⇒B
      where
        A∸x∩B⊆A∩B = ⊆-distrib-∩ (∸-atoms-⊆ A)

        C⊆A∩B : atoms C ⊆ atoms A ∩ atoms B
        C⊆A∩B = A∸x∩B⊆A∩B ∘ C⊆A∸x∩B

        ⊨A⇒C : ⊨ A ⇒ C
        ⊨A⇒C = {!!} --⇒-trans {_} {A} {A ∸ x} {C} (⊨A⇒A∸x A x) ⊨A∸x⇒C
