open import Data.Fin
open import Data.Fin.Subset
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)
open import Data.Vec hiding (_∈_)
open import Data.Product as Product
open import Subset

module Subset.Properties where

∩⇔× : ∀ {n} {p₁ p₂ : Subset n} {x} → x ∈ p₁ ∩ p₂ ⇔ (x ∈ p₁ × x ∈ p₂)
∩⇔× = equivalence (to _ _) from
  where
  to : ∀ {n} (p₁ p₂ : Subset n) {x} → x ∈ p₁ ∩ p₂ → x ∈ p₁ × x ∈ p₂
  to [] [] ()
  to (inside ∷ p₁) (inside ∷ p₂) here = here , here
  to (s₁     ∷ p₁) (s₂     ∷ p₂) (there x∈p₁∩p₂) =
    Product.map there there (to p₁ p₂ x∈p₁∩p₂)

  from : ∀ {n} {p₁ p₂ : Subset n} {x} → x ∈ p₁ × x ∈ p₂ → x ∈ p₁ ∩ p₂
  from (here , here) = here
  from (there x∈p₁ , there x∈p₂) = there (from (x∈p₁ , x∈p₂))

⊆-distrib-∩ : ∀ {n} {p₁ p₂ p₃ : Subset n} → p₁ ⊆ p₂ → p₁ ∩ p₃ ⊆ p₂ ∩ p₃
⊆-distrib-∩ p₁⊆p₂ x∈p₁∩p₃
  with Equivalence.to ∩⇔× ⟨$⟩ x∈p₁∩p₃
...  | x∈p₁ , x∈p₃ = Equivalence.from ∩⇔× ⟨$⟩ (p₁⊆p₂ x∈p₁ , x∈p₃)

diff-⊆ : ∀ {n} (p₁ p₂ : Subset n) → Empty (p₁ − p₂) → p₁ ⊆ p₂
diff-⊆ (inside ∷ p₁) (outside ∷ p₂) ¬∈ here
  with ¬∈ (zero , here)
...  | ()
diff-⊆ (inside ∷ p₁) (inside  ∷ p₂) ¬∈ here = here
diff-⊆ (s₁     ∷ p₁) (s₂      ∷ p₂) ¬∈ (there x∈p₁) =
  there (diff-⊆ _ _ (¬∈ ∘ Product.map suc there) x∈p₁)

⊆-intersection : ∀ {n} {p₁ p₂ : Subset n} → Empty (p₁ − p₂) → p₁ ⊆ p₁ ∩ p₂
⊆-intersection ¬∈ x∈p₁ = Equivalence.from ∩⇔× ⟨$⟩ (x∈p₁ , diff-⊆ _ _ ¬∈ x∈p₁)

−-⊆ : ∀ {n} (p₁ p₂ : Subset n) → p₁ − p₂ ⊆ p₁
−-⊆ [] [] x∈p₁−p₂ = x∈p₁−p₂
−-⊆ (inside ∷ p₁) (outside ∷ p₂) here = here
−-⊆ (_      ∷ p₁) (outside ∷ p₂) (there x∈p₁−p₂) = there (−-⊆ p₁ p₂ x∈p₁−p₂)
−-⊆ (_      ∷ p₁) (inside  ∷ p₂) (there x∈p₁−p₂) = there (−-⊆ p₁ p₂ x∈p₁−p₂)
