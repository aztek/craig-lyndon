open import Data.Nat

module CraigLyndon (n : ℕ) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Data.Vec
open import Data.Bool using (Bool; true; false)
                      renaming (_∧_ to _∧♭_; _∨_ to _∨♭_; not to ¬♭_)

data Formula : Set where
  var : (x : Fin n) → Formula
  ¬_  : (f : Formula) → Formula
  _∧_ : (f g : Formula) → Formula
  _∨_ : (f g : Formula) → Formula
  _⇒_ : (f g : Formula) → Formula

Interpretation = Vec Bool n

eval : Formula → Interpretation → Bool
eval (var x) i = lookup x i
eval (¬ f)   i = ¬♭ eval f i
eval (f ∧ g) i = eval f i ∧♭ eval g i
eval (f ∨ g) i = eval f i ∨♭ eval g i
eval (f ⇒ g) i = (¬♭ eval f i) ∨♭ eval g i

Model : Formula → Interpretation → Set
Model f i = eval f i ≡ true

data ⊨_ (f : Formula) : Set where
  model : ∃ (Model f) → ⊨ f

Atoms = Subset n

atoms : Formula → Atoms
atoms (var x) = ⁅ x ⁆
atoms (¬ f)   = atoms f
atoms (f ∧ g) = atoms f ∪ atoms g
atoms (f ∨ g) = atoms f ∪ atoms g
atoms (f ⇒ g) = atoms f ∪ atoms g

find-interpolant : (φ ψ : Formula) → Formula
find-interpolant = {!!}

interpolates-φ : (φ ψ : Formula) → ⊨ (φ ⇒ ψ) → ⊨ (φ ⇒ find-interpolant φ ψ)
interpolates-φ = {!!}

interpolates-ψ : (φ ψ : Formula) → ⊨ (φ ⇒ ψ) → ⊨ (find-interpolant φ ψ ⇒ ψ)
interpolates-ψ = {!!}

encloses-atoms : (φ ψ : Formula) → ⊨ (φ ⇒ ψ) →
                 atoms (find-interpolant φ ψ) ⊆ atoms ψ ∩ atoms φ
encloses-atoms = {!!}

craig-lyndon : (φ ψ : Formula) → ⊨ (φ ⇒ ψ) →
               ∃ λ ρ → (atoms ρ ⊆ atoms ψ ∩ atoms φ) × ⊨ (φ ⇒ ρ) × ⊨ (ρ ⇒ ψ)
craig-lyndon φ ψ ⊨φ⇒ψ = find-interpolant φ ψ , encloses-atoms φ ψ ⊨φ⇒ψ ,
                        interpolates-φ φ ψ ⊨φ⇒ψ , interpolates-ψ φ ψ ⊨φ⇒ψ 
