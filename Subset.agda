open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Data.Vec hiding (_∈_)

module Subset where

-- Difference between sets
_−_ : ∀ {n} → Subset n → Subset n → Subset n
[] − [] = []
(inside ∷ p₁) − (outside ∷ p₂) = inside  ∷ (p₁ − p₂)
(_      ∷ p₁) − (_       ∷ p₂) = outside ∷ (p₁ − p₂)

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
