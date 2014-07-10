module CraigLyndon where

open import Function
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)

open import Subset
open import Subset.Properties
open import Formula
open import Formula.Properties

interpolate : ∀ {n} (φ ψ : Formula n) → ⊨ φ ⇒ ψ → ∃ λ ρ → (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
interpolate {n} φ ψ = helper φ ψ (induction $ atoms φ − atoms ψ)
  where helper : (φ ψ : Formula n) → Induction (atoms φ − atoms ψ) → ⊨ φ ⇒ ψ →
                 ∃ λ ρ → (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
        helper φ ψ ([] e) ⊨φ⇒ψ = φ , ⊆-intersection e , tautology {n} {φ} , ⊨φ⇒ψ
        helper φ ψ (_∷_ {ρ} ρ∈d i) ⊨φ⇒ψ
          with φ [ ρ / true ] ∨ φ [ ρ / false ]
        ...  | φ′
          with helper φ′ ψ {!!} {!!}
        ...  | χ , a[χ]⊆a[φ′]∩a[ψ] , ⊨φ′⇒χ , ⊨χ⇒ψ = χ , (⊆-distrib-∩ φ′-atoms) ∘ a[χ]⊆a[φ′]∩a[ψ] , ⊨φ⇒χ , ⊨χ⇒ψ
          where ⊨φ⇒φ′ : ⊨ φ ⇒ φ′
                ⊨φ⇒φ′ = {!!}

                ⊨φ′⇒ψ : ⊨ φ′ ⇒ ψ
                ⊨φ′⇒ψ = {!!}

                φ′-atoms : atoms φ′ ⊆ atoms φ
                φ′-atoms = {!!}

                ⊨φ⇒χ = ⇒-trans {n} {φ} {φ′} {χ} ⊨φ⇒φ′ ⊨φ′⇒χ
