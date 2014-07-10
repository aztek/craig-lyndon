open import Data.Bool
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Data.Vec hiding (_∈_)

module Subset where

-- Difference between sets
infixl 5 _−_
_−_ : ∀ {n} → Subset n → Subset n → Subset n
[] − [] = []
s₁ ∷ p₁ − s₂ ∷ p₂ = (s₁ ∧ not s₂) ∷ (p₁ − p₂)

-- Induction over the subset
data Induction {n} (p : Subset n) : Set where
  []  : Empty p → Induction p
  _∷_ : ∀ {x} → x ∈ p → Induction (p [ x ]≔ outside) → Induction p

private
  Empty-[] : Empty []
  Empty-[] (_ , ())

  Empty-outside∷ : ∀ {n} {∅ : Subset n} → Empty ∅ → Empty (outside ∷ ∅)
  Empty-outside∷ _ (zero  , ())
  Empty-outside∷ e (suc x , there x∈∅) = e (x , x∈∅)

  outside∷ : ∀ {n} {p : Subset n} → Induction p → Induction (outside ∷ p)
  outside∷ ([] e)    = [] (Empty-outside∷ e)
  outside∷ (x∈p ∷ i) = there x∈p ∷ outside∷ i

induction : ∀ {n} (p : Subset n) → Induction p
induction [] = [] Empty-[]
induction (inside  ∷ p) = here ∷ outside∷ (induction p)
induction (outside ∷ p) = outside∷ (induction p)
