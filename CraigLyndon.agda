module CraigLyndon where

open import Function
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)

open import Subset
open import Subset.Properties
open import Formula
open import Formula.Properties

CraigLyndon : ∀ {n} → (A B : Formula n) → Set
CraigLyndon A B = ⊨ A ⇒ B → ∃ λ C → (atoms C ⊆ atoms A ∩ atoms B) ⋀ (⊨ A ⇒ C) ⋀ (⊨ C ⇒ B)

interpolate : ∀ {n} (A B : Formula n) → CraigLyndon A B
interpolate {n} A B = helper A B (induction $ atoms A − atoms B)
  where
    helper : ∀ A B → Induction (atoms A − atoms B) → CraigLyndon A B
    helper A B ([] ¬∈) ⊨A⇒B = A , A⊆A∩B , ⊨A⇒A , ⊨A⇒B
      where
        A⊆A∩B : atoms A ⊆ atoms A ∩ atoms B
        A⊆A∩B = ⊆-intersection ¬∈

        ⊨A⇒A = tautology {n} {A}

    helper A B (_∷_ {x} x∈d i) ⊨A⇒B
      with elim-var A x
    ...  | A′
      with helper A′ B {!!} {!!}
    ...  | C , C⊆A′∩B , ⊨A′⇒C , ⊨C⇒B = C , C⊆A∩B , ⊨A⇒C , ⊨C⇒B
      where
        ⊨A⇒A′ : ⊨ A ⇒ A′
        ⊨A⇒A′ = {!!}

        ⊨A′⇒B : ⊨ A′ ⇒ B
        ⊨A′⇒B = {!!}

        A′⊆A : atoms A′ ⊆ atoms A
        A′⊆A = {!!}

        A′∩B⊆A∩B : atoms A′ ∩ atoms B ⊆ atoms A ∩ atoms B
        A′∩B⊆A∩B = ⊆-distrib-∩ A′⊆A

        C⊆A∩B : atoms C ⊆ atoms A ∩ atoms B
        C⊆A∩B = A′∩B⊆A∩B ∘ C⊆A′∩B

        ⊨A⇒C = ⇒-trans {n} {A} {A′} {C} ⊨A⇒A′ ⊨A′⇒C
