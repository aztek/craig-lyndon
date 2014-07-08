open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Subset.Props
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)
open import Data.Nat using (zero; suc)
open import Data.Vec hiding (_∈_)
open import Data.Product as Product
open import Data.Empty using (⊥-elim)
open import Subset

module Subset.Properties where

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
⊆-itself x∈xs = x∈xs

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

∩⇔× : ∀ {n} {p₁ p₂ : Subset n} {x} → (x ∈ p₁ × x ∈ p₂) ⇔ x ∈ p₁ ∩ p₂
∩⇔× = equivalence to (from _ _)
  where
  to : ∀ {n} {p₁ p₂ : Subset n} {x} → x ∈ p₁ × x ∈ p₂ → x ∈ p₁ ∩ p₂
  to (here , here) = here
  to (there x∈p₁ , there x∈p₂) = there (to (x∈p₁ , x∈p₂))

  from : ∀ {n} (p₁ p₂ : Subset n) {x} → x ∈ p₁ ∩ p₂ → x ∈ p₁ × x ∈ p₂
  from [] [] ()
  from (inside ∷ p₁) (inside ∷ p₂) here = here , here
  from (s₁     ∷ p₁) (s₂     ∷ p₂) (there x∈p₁∩p₂) =
    Product.map there there (from p₁ p₂ x∈p₁∩p₂)

⊆-distrib-∩ : ∀ {n} {p₁ p₂ p₃ : Subset n} → p₁ ⊆ p₂ → p₁ ∩ p₃ ⊆ p₂ ∩ p₃
⊆-distrib-∩ p₁⊆p₂ x∈p₁∩p₃
  with Equivalence.from ∩⇔× ⟨$⟩ x∈p₁∩p₃
...  | x∈p₁ , x∈p₃ = Equivalence.to ∩⇔× ⟨$⟩ (p₁⊆p₂ x∈p₁ , x∈p₃)

⊆-trans : ∀ {n} {p₁ p₂ p₃ : Subset n} → p₁ ⊆ p₂ → p₂ ⊆ p₃ → p₁ ⊆ p₃
⊆-trans p₁⊆p₂ p₂⊆p₃ = p₂⊆p₃ ∘ p₁⊆p₂
