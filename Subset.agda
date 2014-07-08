module Subset where

open import Function
open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Data.Fin.Subset.Props
open import Data.Nat
open import Data.Product as Product
open import Data.Vec as Vec hiding ([_]; _∈_)

replicate-all : ∀ {n} {A : Set} {a : A} (x : Fin n) → replicate a [ x ]= a
replicate-all zero = here
replicate-all (suc x) = there (replicate-all x)

outside-∉ : ∀ {n} {x} {p : Subset n} → p [ x ]= outside → x ∉ p
outside-∉ here ()
outside-∉ (there x∉p) (there x∈p) = outside-∉ x∉p x∈p

∅ : ∀ {n} → Subset n
∅ = replicate outside

Empty-∅ : ∀ {n} → Empty {n} ∅
Empty-∅ (x , x∈∅) = outside-∉ (replicate-all x) x∈∅

_−_ : ∀ {n} → Subset n → Subset n → Subset n
[] − [] = []
(inside ∷ α*) − (outside ∷ β*) = inside  ∷ (α* − β*)
(_      ∷ α*) − (_       ∷ β*) = outside ∷ (α* − β*)

⊆-diff : ∀ {n} (α* β* : Subset n) {x} → x ∈ α* − β* → x ∈ α*
⊆-diff [] [] ()
⊆-diff (inside  ∷ α*) (outside ∷ β*) here = here
⊆-diff (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)
⊆-diff (inside  ∷ α*) (inside  ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)
⊆-diff (outside ∷ α*) (_       ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)

⊈-diff : ∀ {n} (α* β* : Subset n) {x} → x ∈ α* − β* → x ∉ β*
⊈-diff [] [] ()
⊈-diff (inside  ∷ α*) (outside ∷ β*) here = λ ()
⊈-diff (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there
⊈-diff (inside  ∷ α*) (inside  ∷ β*) {zero} ()
⊈-diff (inside  ∷ α*) (inside  ∷ β*) {suc _} (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there
⊈-diff (outside ∷ α*) (_       ∷ β*) {zero} ()
⊈-diff (outside ∷ α*) (_       ∷ β*) {suc _} (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there

drop-suc : ∀ m n → suc m ≤′ suc n → m ≤′ n
drop-suc zero zero s = ≤′-refl
drop-suc zero (suc n) (≤′-step s) = ≤′-step (drop-suc zero n s)
drop-suc (suc m) zero (≤′-step ())
drop-suc (suc .n) (suc n) ≤′-refl = ≤′-refl
drop-suc (suc m) (suc n) (≤′-step s) = ≤′-step (drop-suc (suc m) n s)

fromℕ≤′ : ∀ m n → m <′ n → Fin n
fromℕ≤′ _ zero ()
fromℕ≤′ zero (suc n) _ = zero
fromℕ≤′ (suc m) (suc n) m<′n = suc (fromℕ≤′ m n (drop-suc (suc m) n m<′n))

drop-suc₂ : ∀ m n → suc m ≤′ n → m ≤′ n
drop-suc₂ zero zero ()
drop-suc₂ zero (suc .0) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ zero (suc n) (≤′-step s) = ≤′-step (drop-suc₂ zero n s)
drop-suc₂ (suc m) zero ()
drop-suc₂ (suc m) (suc .(suc m)) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ (suc m) (suc n) (≤′-step s) = ≤′-step (drop-suc₂ (suc m) n s)

-- Induction over the subset
data Induction {n} (p : Subset n) : Set where
  []  : Empty p → Induction p
  _∷_ : ∀ {x} → x ∈ p → Induction (p [ x ]≔ outside) → Induction p

induction : ∀ {n} (α* : Subset n) → Induction α*
induction {n} α* = helper {n} {≤′-refl} ∅ ([] Empty-∅) α*
  where Empty-outside : ∀ {n} {p : Subset n} → Empty p → Empty (outside ∷ p)
        Empty-outside _ (zero , ())
        Empty-outside e (suc x , there x∈p) = e (x , x∈p)

        ∷-induction : ∀ {n} (p : Subset n) → Induction p → Induction (outside ∷ p)
        ∷-induction p ([] e) = [] (Empty-outside e)
        ∷-induction p (_∷_ {x} x∈p i) = there x∈p ∷ ∷-induction (p [ x ]≔ outside) i

        helper : {m : ℕ} {m≤n : m ≤′ n} (acc : Subset n) (ind-acc : Induction acc) (β* : Subset m) → Induction β*
        helper {zero}  {0<n} _ _ [] = [] (λ { (_ , ()) })
        helper {suc m} {m<n} a i (inside  ∷ p) = here ∷ ∷-induction p (helper {m} {drop-suc₂ m n m<n} a i p)
        helper {suc m} {m<n} a i (outside ∷ p) = ∷-induction p (helper {m} {drop-suc₂ m n m<n} a i p)

diff-⊆ : ∀ {n} {xs ys : Subset n} → Empty (xs − ys) → xs ⊆ ys
diff-⊆ {n} {xs} {ys} p {x} = helper xs ys p x
  where
    helper : ∀ {m} (xs ys : Subset m) → Empty (xs − ys) →
             ∀ α → α ∈ xs → α ∈ ys
    helper [] [] _ _ ()
    helper (inside  ∷ xs) (inside  ∷ ys) _ zero _ = here
    helper (inside  ∷ xs) (inside  ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ Product.map suc there) α α∈xs)
    helper (inside  ∷ xs) (outside ∷ ys) e zero here = ⊥-elim $ e (zero , here)
    helper (inside  ∷ xs) (outside ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ const (zero , here)) α α∈xs)
    helper (outside ∷ xs) (_       ∷ ys) e zero ()
    helper (outside ∷ xs) (_       ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ Product.map suc there) α α∈xs)

⊆-itself : ∀ {n} {xs : Subset n} → xs ⊆ xs
⊆-itself = λ {_} {_} {_} z → z

⊆-intersection : ∀ {n} {xs ys : Subset n} → xs ⊆ ys → xs ⊆ xs ∩ ys
⊆-intersection {zero}  {[]} {[]} _ = λ z → z
⊆-intersection {suc n} {x ∷ xs} {y ∷ ys} xs⊆ys = helper
  where
    open import Relation.Binary.PropositionalEquality

    drop-here : ∀ {n} {s} {p : Subset n} → zero ∈ s ∷ p → s ≡ inside
    drop-here here = refl

    helper : x ∷ xs ⊆ (x ∷ xs) ∩ (y ∷ ys)
    helper {zero}  z∈i rewrite drop-here z∈i | drop-here (xs⊆ys z∈i) = here
    helper {suc z} s∈i = there (⊆-intersection (drop-there ∘ xs⊆ys ∘ there) (drop-there s∈i))

encloses-own-atoms : ∀ {n} {xs ys : Subset n} → Empty (xs − ys) → xs ⊆ xs ∩ ys
encloses-own-atoms = ⊆-intersection ∘ diff-⊆

-- TODO
postulate ⊆-distrib-∩ : ∀ {n} {xs xs′ ys : Subset n} → xs ⊆ xs′ → xs ∩ ys ⊆ xs′ ∩ ys
--⊆-distrib-∩ = {!!}

-- TODO
postulate ⊆-trans : ∀ {n} {xs ys zs : Subset n} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
--⊆-trans = {!!}
