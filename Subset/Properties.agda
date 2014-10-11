open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Subset.Props
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)
open import Data.Vec hiding (_∈_)
open import Data.Product as Product
open import Relation.Binary.PropositionalEquality
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
−-⊆ [] [] ()
−-⊆ (inside ∷ p₁) (outside ∷ p₂) here = here
−-⊆ (_      ∷ p₁) (_       ∷ p₂) (there x∈p₁−p₂) = there (−-⊆ p₁ p₂ x∈p₁−p₂)

∅ : ∀ {n} → Subset n
∅ = replicate outside

Empty-∅ : ∀ {n} → Empty (∅ {n})
Empty-∅ (zero , ())
Empty-∅ (suc x , there x∈∅) = Empty-∅ (x , x∈∅)

∅−p=∅ : ∀ {n} {p : Subset n} → ∅ − p ≡ ∅
∅−p=∅ {p = []} = refl
∅−p=∅ {p = _ ∷ _} = cong (_∷_ outside) ∅−p=∅

p−∅=p : ∀ {n} {p : Subset n} → p − ∅ ≡ p
p−∅=p {p = []} = refl
p−∅=p {p = inside  ∷ p} = cong (_∷_ inside)  p−∅=p
p−∅=p {p = outside ∷ p} = cong (_∷_ outside) p−∅=p

p−p=∅ : ∀ {n} {p : Subset n} → p − p ≡ ∅
p−p=∅ {p = []} = refl
p−p=∅ {p = inside  ∷ _} = cong (_∷_ outside) p−p=∅
p−p=∅ {p = outside ∷ _} = cong (_∷_ outside) p−p=∅

∪-idempotence : ∀ {n} {p : Subset n} → p ∪ p ≡ p
∪-idempotence {p = []} = refl
∪-idempotence {p = inside  ∷ _} = cong (_∷_ inside)  ∪-idempotence
∪-idempotence {p = outside ∷ _} = cong (_∷_ outside) ∪-idempotence

x∉⁅y⁆ : ∀ {n} (x y : Fin n) → x ≢ y → x ∉ ⁅ y ⁆
x∉⁅y⁆ zero zero x≠y = ⊥-elim (x≠y refl)
x∉⁅y⁆ zero (suc y) x≠y = λ ()
x∉⁅y⁆ (suc x) zero x≠y = x∉∅ ∘ drop-there where x∉∅ = curry Empty-∅ x
x∉⁅y⁆ (suc x) (suc y) x≠y = x∉⁅y⁆ x y (x≠y ∘ cong suc) ∘ drop-there

−-var : ∀ {n} (p : Subset n) x → x ∉ p → p − ⁅ x ⁆ ≡ p
−-var [] () x∈p
−-var (inside  ∷ p) zero x∈p = ⊥-elim (x∈p here)
−-var (outside ∷ p) zero x∈p = cong (_∷_ outside) p−∅=p
−-var (inside  ∷ p) (suc x) x∈p = cong (_∷_ inside)  (−-var p x (x∈p ∘ there))
−-var (outside ∷ p) (suc x) x∈p = cong (_∷_ outside) (−-var p x (x∈p ∘ there))

open import Data.Bool using (not)
open import Data.Bool.Properties
open RingSolver hiding (∅)

−-distrib-∪ : ∀ {n} {p₁ p₂ p₃ : Subset n} → (p₁ − p₃) ∪ (p₂ − p₃) ≡ p₁ ∪ p₂ − p₃
−-distrib-∪ {p₁ = []} {[]} {[]} = refl
−-distrib-∪ {p₁ = s₁ ∷ _} {s₂ ∷ _} {s₃ ∷ _} =
  cong₂ _∷_ (solve 3 (λ s₁ s₂ s₃ → (s₁ :* s₃) :+ (s₂ :* s₃) := (s₁ :+ s₂) :* s₃) refl s₁ s₂ (not s₃)) −-distrib-∪
