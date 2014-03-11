open import Data.Nat

module CraigLyndon (n : ℕ) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)
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

infixl 5 ⊨_ 
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

module Properties (φ ψ : Formula)
                  (⊨φ⇒ψ : ⊨ φ ⇒ ψ) where
  ρ = find-interpolant φ ψ

  interpolates-φ : ⊨ φ ⇒ ρ
  interpolates-φ = {!!}

  interpolates-ψ : ⊨ ρ ⇒ ψ
  interpolates-ψ = {!!}

  encloses-atoms : atoms ρ ⊆ atoms ψ ∩ atoms φ
  encloses-atoms = {!!}

  craig-lyndon : (atoms ρ ⊆ atoms ψ ∩ atoms φ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
  craig-lyndon = encloses-atoms , interpolates-φ , interpolates-ψ 
