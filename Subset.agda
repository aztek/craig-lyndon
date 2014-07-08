module Subset where

open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Data.Nat
open import Data.Product
open import Data.Vec hiding (_∈_)

-- Empty set
∅ : ∀ {n} → Subset n
∅ = replicate outside

-- Difference between sets
_−_ : ∀ {n} → Subset n → Subset n → Subset n
[] − [] = []
(inside ∷ α*) − (outside ∷ β*) = inside  ∷ (α* − β*)
(_      ∷ α*) − (_       ∷ β*) = outside ∷ (α* − β*)

-- Induction over the subset
data Induction {n} (p : Subset n) : Set where
  []  : Empty p → Induction p
  _∷_ : ∀ {x} → x ∈ p → Induction (p [ x ]≔ outside) → Induction p

induction : ∀ {n} (α* : Subset n) → Induction α*
induction {n} = helper {n} {≤′-refl} ∅ ([] Empty-∅)
  where replicate-all : ∀ {n} {A : Set} {a : A} (x : Fin n) → replicate a [ x ]= a
        replicate-all zero = here
        replicate-all (suc x) = there (replicate-all x)

        outside-∉ : ∀ {n} {x} {p : Subset n} → p [ x ]= outside → x ∉ p
        outside-∉ here ()
        outside-∉ (there x∉p) (there x∈p) = outside-∉ x∉p x∈p

        Empty-∅ : ∀ {n} → Empty {n} ∅
        Empty-∅ (x , x∈∅) = outside-∉ (replicate-all x) x∈∅

        Empty-outside : ∀ {n} {p : Subset n} → Empty p → Empty (outside ∷ p)
        Empty-outside _ (zero , ())
        Empty-outside e (suc x , there x∈p) = e (x , x∈p)

        ∷-induction : ∀ {n} (p : Subset n) → Induction p → Induction (outside ∷ p)
        ∷-induction p ([] e) = [] (Empty-outside e)
        ∷-induction p (_∷_ {x} x∈p i) = there x∈p ∷ ∷-induction (p [ x ]≔ outside) i

        drop-suc : ∀ m n → suc m ≤′ n → m ≤′ n
        drop-suc  m zero    ()
        drop-suc .n (suc n) ≤′-refl = ≤′-step ≤′-refl
        drop-suc  m (suc n) (≤′-step s) = ≤′-step (drop-suc m n s)

        helper : {m : ℕ} {m≤n : m ≤′ n} (acc : Subset n) (ind-acc : Induction acc) (β* : Subset m) → Induction β*
        helper {zero}  {0<n} _ _ [] = [] (λ { (_ , ()) })
        helper {suc m} {m<n} a i (inside  ∷ p) = here ∷ ∷-induction p (helper {m} {drop-suc m n m<n} a i p)
        helper {suc m} {m<n} a i (outside ∷ p) = ∷-induction p (helper {m} {drop-suc m n m<n} a i p)
