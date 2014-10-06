module CraigLyndon where

open import Function
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Vec hiding (_∈_)

open import Subset
open import Subset.Properties
open import Formula
open import Formula.Properties

CraigLyndon : ∀ {n} → (A B : Formula n) → Set
CraigLyndon A B = ⊨ A ⇒ B → ∃ λ C → (atoms C ⊆ atoms A ∩ atoms B) ⋀ (⊨ A ⇒ C) ⋀ (⊨ C ⇒ B)

data Δ-Atoms {n} (A B : Formula n) : Set where
  [] : Empty (atoms A − atoms B) → Δ-Atoms A B
  _∶_∷_ : ∀ x → x ∈ (atoms A − atoms B) → Δ-Atoms (A ∸ x) B → Δ-Atoms A B

diff : ∀ {n} (p₁ p₂ : Subset n) → Set
diff p₁ p₂ = ∀ {x} → x ∈ p₁ → x ∉ p₂

Δ-atoms : ∀ {n} (A B : Formula n) → Δ-Atoms A B
Δ-atoms A B = {!!}

⊨A∸x⇒B : ∀ {n} {A B : Formula n} x → ⊨ A ⇒ B → ⊨ A ∸ x ⇒ B
⊨A∸x⇒B = {!!}

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Data.Empty
open import Data.Fin
open import Data.Fin.Props

∅ : ∀ {n} → Subset n
∅ = replicate outside

∅−p=∅ : ∀ {n} {p : Subset n} → ∅ − p ≡ ∅
∅−p=∅ {p = []} = refl
∅−p=∅ {p = _ ∷ _} = cong (_∷_ outside) ∅−p=∅

p−∅=p : ∀ {n} {p : Subset n} → p − ∅ ≡ p
p−∅=p {p = []} = refl
p−∅=p {p = x ∷ p} = cong₂ _∷_ {!!} p−∅=p

p−p=∅ : ∀ {n} {p : Subset n} → p − p ≡ ∅
p−p=∅ {p = []} = refl
p−p=∅ {p = s ∷ _} = cong₂ _∷_ {!!} p−p=∅

∪-idenpotence : ∀ {n} {p : Subset n} → p ∪ p ≡ p
∪-idenpotence {p = []} = refl
∪-idenpotence {p = s ∷ _} = cong₂ _∷_ {!!} ∪-idenpotence

−-distrib-∪ : ∀ {n} {A B C : Subset n} → (A − C) ∪ (B − C) ≡ A ∪ B − C
−-distrib-∪ {A = []} {[]} {[]} = refl
−-distrib-∪ {A = a ∷ _} {b ∷ _} {c ∷ _} = cong₂ _∷_ {!!} −-distrib-∪

var-elim : ∀ {n} (A : Formula n) x {c} → Constant c → atoms (A [ x / c ]) ≡ atoms A − ⁅ x ⁆
var-elim true  _ _ = sym ∅−p=∅
var-elim false _ _ = sym ∅−p=∅
var-elim (var y) x c
  with y ≟ x
...  | yes y≡x rewrite y≡x = trans (atoms-const c) (sym p−p=∅)
                             where atoms-const : ∀ {n} {c : Formula n} → Constant c → atoms c ≡ ∅
                                   atoms-const true  = refl
                                   atoms-const false = refl
...  | no  y≢x = sym (lemma y x y≢x)
                 where lemma : ∀ {n} (y x : Fin n) → y ≢ x → ⁅ y ⁆ − ⁅ x ⁆ ≡ ⁅ y ⁆
                       lemma zero zero y≢x = ⊥-elim (y≢x refl)
                       lemma zero (suc x) _ = cong (_∷_ inside)  ∅−p=∅
                       lemma (suc y) zero _ = cong (_∷_ outside) p−∅=p
                       lemma (suc y) (suc x) y≢x = cong (_∷_ outside) (lemma y x (y≢x ∘ cong suc))
var-elim (! A) x c = var-elim A x c
var-elim (A ∧ B) x c rewrite var-elim A x c | var-elim B x c = −-distrib-∪
var-elim (A ∨ B) x c rewrite var-elim A x c | var-elim B x c = −-distrib-∪
var-elim (A ⇒ B) x c rewrite var-elim A x c | var-elim B x c = −-distrib-∪

−-∸ : ∀ {n} (A : Formula n) x → atoms (A ∸ x) ≡ atoms A − ⁅ x ⁆
−-∸ A x rewrite var-elim A x true | var-elim A x false = ∪-idenpotence

∸-atoms-⊆ : ∀ {n} (A : Formula n) {x} → atoms (A ∸ x) ⊆ atoms A
∸-atoms-⊆ A {x} rewrite −-∸ A x = −-⊆ (atoms A) ⁅ x ⁆

open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence; module Equivalence)

interpolate : ∀ {n} (A B : Formula n) → CraigLyndon A B
interpolate A B = helper A B (Δ-atoms _ _)
  where
    helper : ∀ A B → Δ-Atoms A B → CraigLyndon A B
    helper A B ([] ¬∈) ⊨A⇒B = A , A⊆A∩B , ⊨A⇒A , ⊨A⇒B
      where
        A⊆A∩B = ⊆-intersection ¬∈
        ⊨A⇒A  = tautology A
    helper A B (x ∶ x∈Δ ∷ i) ⊨A⇒B
      with helper (A ∸ x) B i (⊨A∸x⇒B {_} {A} {B} x ⊨A⇒B)
    ...  | C , C⊆A∸x∩B , ⊨A∸x⇒C , ⊨C⇒B = C , C⊆A∩B , ⊨A⇒C , ⊨C⇒B
      where
        A∸x∩B⊆A∩B = ⊆-distrib-∩ (∸-atoms-⊆ A)

        C⊆A∩B : atoms C ⊆ atoms A ∩ atoms B
        C⊆A∩B = A∸x∩B⊆A∩B ∘ C⊆A∸x∩B

        ⊨A⇒C = ⇒-trans {_} {A} {A ∸ x} {C} (⊨A⇒A∸x A x) ⊨A∸x⇒C
