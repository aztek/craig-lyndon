module CraigLyndon where

open import Function
open import Data.Nat using (ℕ)
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Vec hiding (_∈_)

open import Subset
open import Subset.Properties
open import Formula
open import Formula.Properties

CraigLyndon : ∀ {n} → (A B : Formula n) → Set
CraigLyndon A B = ⊨ A ⇒ B → ∃ λ C → (atoms C ⊆ atoms A ∩ atoms B) ⋀ (⊨ A ⇒ C) ⋀ (⊨ C ⇒ B)

data Δ-Atoms {n} (A B : Formula n) : Set where
  []  : Empty (atoms A − atoms B) → Δ-Atoms A B
  _∷_ : ∀ {x} → x ∈ atoms A − atoms B → Δ-Atoms (A ∸ x) B → Δ-Atoms A B

diff : ∀ {n} (p₁ p₂ : Subset n) → Set
diff p₁ p₂ = ∀ {x} → x ∈ p₁ → x ∉ p₂

Δ-atoms : ∀ {n} (A B : Formula n) → Δ-Atoms A B
Δ-atoms A B = {!!}

⊨A∸x⇒B : ∀ {n} {A B : Formula n} x → ⊨ A ⇒ B → ⊨ A ∸ x ⇒ B
⊨A∸x⇒B = {!!}

open import Relation.Binary.PropositionalEquality
open import Data.Fin

−-∸ : ∀ {n} (A : Formula n) x → atoms (A ∸ x) ≡ atoms A − ⁅ x ⁆
−-∸ A x = {!!}

∸-atoms-⊆ : ∀ {n} (A : Formula n) {x} → atoms (A ∸ x) ⊆ atoms A
∸-atoms-⊆ A {x} rewrite −-∸ A x = −-⊆ (atoms A) ⁅ x ⁆

open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)

interpolate : ∀ {n} (A B : Formula n) → CraigLyndon A B
interpolate A B = helper A B (Δ-atoms _ _)
  where
    helper : ∀ A B → Δ-Atoms A B → CraigLyndon A B
    helper A B ([] ¬∈) ⊨A⇒B = A , A⊆A∩B , ⊨A⇒A , ⊨A⇒B
      where
        A⊆A∩B = ⊆-intersection ¬∈
        ⊨A⇒A  = tautology A
    helper A B (_∷_ {x} x∈Δ i) ⊨A⇒B
      with helper (A ∸ x) B i (⊨A∸x⇒B {_} {A} {B} x ⊨A⇒B)
    ...  | C , C⊆A∸x∩B , ⊨A∸x⇒C , ⊨C⇒B = C , C⊆A∩B , ⊨A⇒C , ⊨C⇒B
      where
        A∸x∩B⊆A∩B = ⊆-distrib-∩ (∸-atoms-⊆ A)

        C⊆A∩B : atoms C ⊆ atoms A ∩ atoms B
        C⊆A∩B = A∸x∩B⊆A∩B ∘ C⊆A∸x∩B

        ⊨A⇒C = ⇒-trans {_} {A} {A ∸ x} {C} (⊨A⇒A∸x A x) ⊨A∸x⇒C
