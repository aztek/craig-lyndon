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
        helper φ ψ ([] e) ⊨φ⇒ψ = φ , encloses-own-atoms e , tautology {n} {φ} , ⊨φ⇒ψ
        helper φ ψ (_∷_ {ρ} ρ∈d i) ⊨φ⇒ψ
          with φ [ ρ / true ] ∨ φ [ ρ / false ]
        ...  | φ′ = χ , ⊆-trans χ-atoms (⊆-distrib-∩ φ′-atoms) , ⇒-trans {n} {φ} {φ′} {χ} ⊨φ⇒φ′ ⊨φ′⇒χ , ⊨χ⇒ψ
          where hyp : ∃ λ χ → (atoms χ ⊆ atoms φ′ ∩ atoms ψ) ⋀ (⊨ φ′ ⇒ χ) ⋀ (⊨ χ ⇒ ψ)
                hyp = {!!}

                χ : Formula n
                χ = proj₁ hyp

                χ-atoms : atoms χ ⊆ atoms φ′ ∩ atoms ψ
                χ-atoms = proj₁ (proj₂ hyp)

                ⊨φ′⇒χ : ⊨ φ′ ⇒ χ
                ⊨φ′⇒χ = proj₁ (proj₂ (proj₂ hyp))

                ⊨χ⇒ψ : ⊨ χ ⇒ ψ
                ⊨χ⇒ψ = proj₂ (proj₂ (proj₂ hyp))

                ⊨φ⇒φ′ : ⊨ φ ⇒ φ′
                ⊨φ⇒φ′ = {!!}

                φ′-atoms : atoms φ′ ⊆ atoms φ
                φ′-atoms = {!!}
