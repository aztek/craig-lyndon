open import Data.Fin
open import Data.Fin.Subset
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)
open import Data.Vec hiding (_∈_)
open import Data.Product as Product
open import Subset

module Subset.Properties where

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

diff-⊆ : ∀ {n} (p₁ p₂ : Subset n) → Empty (p₁ − p₂) → p₁ ⊆ p₂
diff-⊆ (inside ∷ p₁) (outside ∷ p₂) ¬∈ here
  with ¬∈ (zero , here)
...  | ()
diff-⊆ (inside ∷ p₁) (inside  ∷ p₂) ¬∈ here = here
diff-⊆ (s₁     ∷ p₁) (s₂      ∷ p₂) ¬∈ (there x∈p₁) = there (diff-⊆ _ _ (¬∈ ∘ Product.map suc there) x∈p₁)

⊆-intersection : ∀ {n} {p₁ p₂ : Subset n} → Empty (p₁ − p₂) → p₁ ⊆ p₁ ∩ p₂
⊆-intersection ¬∈ x∈p₁ = Equivalence.to ∩⇔× ⟨$⟩ (x∈p₁ , diff-⊆ _ _ ¬∈ x∈p₁)
