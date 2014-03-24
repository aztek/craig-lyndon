open import Data.Nat

module CraigLyndon (n : ℕ) where

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Vec hiding ([_]; _∈_)
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

∣_−_∣ : ∀ {n} → Subset n → Subset n → ℕ
∣ [] − [] ∣ = 0
∣ inside ∷ xs − outside ∷ ys ∣ = suc ∣ xs − ys ∣
∣ _      ∷ xs − _       ∷ ys ∣ = ∣ xs − ys ∣

find-interpolant : (φ ψ : Formula) → Formula
find-interpolant φ ψ
  with ∣ atoms φ − atoms ψ ∣
...    | 0 = φ
...    | suc m = {!!}

module Properties (φ ψ : Formula)
                  (⊨φ⇒ψ : ⊨ φ ⇒ ψ) where
  open import Relation.Binary.PropositionalEquality
  open import Data.Fin.Subset.Props

  private
    tautology : ∀ {χ} → ⊨ χ ⇒ χ
    tautology {χ} = model (interpretation , helper χ interpretation)
      where
        interpretation : Interpretation
        interpretation = replicate true

        helper : ∀ f i → eval (f ⇒ f) i ≡ true
        helper f i
          with eval f i
        ...  | true = refl
        ...  | false = refl

  ρ = find-interpolant φ ψ

  interpolates-φ : ⊨ φ ⇒ ρ
  interpolates-φ
    with ∣ atoms φ − atoms ψ ∣
  ...    | 0 = tautology
  ...    | suc m = {!!}

  interpolates-ψ : ⊨ ρ ⇒ ψ
  interpolates-ψ
    with ∣ atoms φ − atoms ψ ∣
  ...    | 0 = ⊨φ⇒ψ
  ...    | suc m = {!!}

  private
    diff-⊆ : ∀ {n} {xs ys : Subset n} → ∣ xs − ys ∣ ≡ 0 → xs ⊆ ys
    diff-⊆ {n} {xs} {ys} p {x} = helper xs ys p x
      where
        helper : ∀ {n} (xs ys : Subset n) → ∣ xs − ys ∣ ≡ 0 →
                 ∀ atom → atom ∈ xs → atom ∈ ys
        helper [] [] _ _ ()
        helper (inside ∷ _) (outside ∷ _) () _ _
        helper (inside ∷ xs) (inside ∷ ys) _ zero here = here
        helper (inside ∷ xs) (inside ∷ ys) p (suc atom) (there a∈xs) = there (helper xs ys p atom a∈xs)
        helper (outside ∷ _) (_ ∷ _) _ zero ()
        helper (outside ∷ xs) (_ ∷ ys) p (suc atom) (there a∈xs) = there (helper xs ys p atom a∈xs)

    ⊆-intersection : ∀ {n} {xs ys : Subset n} → xs ⊆ ys → xs ⊆ xs ∩ ys
    ⊆-intersection {zero}  {[]} {[]} _ = λ z → z
    ⊆-intersection {suc n} {x ∷ xs} {y ∷ ys} p = helper
      where
        drop-here : ∀ {n} {x} {xs : Subset n} → x ∷ xs [ zero ]= inside → x ≡ inside
        drop-here here = refl

        helper : (x ∷ xs) ⊆ (x ∷ xs) ∩ (y ∷ ys)
        helper {zero}  q rewrite drop-here q | drop-here (p q) = here
        helper {suc z} q = there (⊆-intersection (drop-there ∘ p ∘ there) (drop-there q))

    encloses-own-atoms : ∀ {xs ys : Atoms} → ∣ xs − ys ∣ ≡ 0 → xs ⊆ xs ∩ ys
    encloses-own-atoms = ⊆-intersection ∘ diff-⊆

  encloses-atoms : atoms ρ ⊆ atoms φ ∩ atoms ψ
  encloses-atoms
    with ∣ atoms φ − atoms ψ ∣
       | inspect (λ as → ∣ atoms φ − as ∣) (atoms ψ)
  ...  | 0     | [ e ] = encloses-own-atoms e
  ...  | suc m | [ e ] = {!!}

  craig-lyndon : (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
  craig-lyndon = encloses-atoms , interpolates-φ , interpolates-ψ 
