open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Data.Empty
open import Data.Nat using (ℕ)
open import Data.Fin.Subset
open import Data.Fin.Subset.Props
open import Data.Vec hiding ([_]; _∈_)
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool as B using (Bool; T) renaming (not to ¬♭_; _∨_ to _∨♭_; _∧_ to _∧♭_)
open import Data.Bool.Properties
--open RingSolver
import Data.Unit as Unit
open import Data.Product as Product renaming (_×_ to _⋀_)
open import Function.Equivalence using (Equivalence; module Equivalence)
open import Function.Equality hiding (cong; _∘_)
open import Function

open import Formula
open import Subset
open import Subset.Properties

module Formula.Properties where

/-atoms : ∀ {n} (A : Formula n) x c → atoms (A [ x / ⌜ c ⌝ ]) ≡ atoms A − ⁅ x ⁆
/-atoms true  _ _ = sym ∅−p=∅
/-atoms false _ _ = sym ∅−p=∅
/-atoms (var y) x c
  with y ≟ x
...  | no  y≠x = sym $ −-var ⁅ y ⁆ x (x∉⁅y⁆ x y (y≠x ∘ sym))
...  | yes y=x rewrite y=x
  with c
...  | B.true  = sym p−p=∅
...  | B.false = sym p−p=∅
/-atoms (! A) x c = /-atoms A x c
/-atoms (A ∧ B) x c rewrite /-atoms A x c | /-atoms B x c = −-distrib-∪
/-atoms (A ∨ B) x c rewrite /-atoms A x c | /-atoms B x c = −-distrib-∪
/-atoms (A ⇒ B) x c rewrite /-atoms A x c | /-atoms B x c = −-distrib-∪

−-∸ : ∀ {n} (A : Formula n) x → atoms (A ∸ x) ≡ atoms A − ⁅ x ⁆
−-∸ A x rewrite /-atoms A x B.true | /-atoms A x B.false = ∪-idempotence

∸-atoms-⊆ : ∀ {n} (A : Formula n) {x} → atoms (A ∸ x) ⊆ atoms A
∸-atoms-⊆ A {x} rewrite −-∸ A x = −-⊆ (atoms A) ⁅ x ⁆

tautology : ∀ {n} (A : Formula n) → ⊨ A ⇒ A
tautology A = i , model
  where
    i = replicate B.true
    model : T (eval (A ⇒ A) i)
    model with eval A i
    ... | B.true  = Unit.tt
    ... | B.false = Unit.tt

/-eval : ∀ {n} (A : Formula n) (c : Bool) x {i} → lookup x i ≡ c → eval (A [ x / ⌜ c ⌝ ]) i ≡ eval A i
/-eval true  c x Tx = refl
/-eval false c x Tx = refl
/-eval (var y) c x Tx
  with y ≟ x
...  | no y≠x = refl
...  | yes y=x rewrite y=x
  with c 
...  | B.true  = sym Tx
...  | B.false = sym Tx
/-eval (! A)   c x Tx = cong ¬♭_   (/-eval A c x Tx)
/-eval (A ∧ B) c x Tx = cong₂ _∧♭_ (/-eval A c x Tx) (/-eval B c x Tx)
/-eval (A ∨ B) c x Tx = cong₂ _∨♭_ (/-eval A c x Tx) (/-eval B c x Tx)
/-eval (A ⇒ B) c x Tx = cong₂ (λ a b → ¬♭ a ∨♭ b) (/-eval A c x Tx) (/-eval B c x Tx)

lemma : ∀ b → T (b ∨♭ B.true)
lemma B.true  = Unit.tt
lemma B.false = Unit.tt


⊨A⇒A∸x : ∀ {n} (A : Formula n) x → ⊨ A ⇒ A ∸ x
⊨A⇒A∸x A x = i , model
  where
    i = replicate B.true
    model : T (eval (A ⇒ A ∸ x) i)
    model
      with eval A i | inspect (eval A) i
    ...  | B.false  | _ = Unit.tt
    ...  | B.true   | [ q ]
      with lookup x i | inspect (lookup x) i
    ...  | B.true     | [ e ] rewrite /-eval A B.true x e | q = Unit.tt
    ...  | B.false    | [ e ]
      rewrite /-eval A B.false x e | q = lemma (eval (A [ x / true ]) i)

-- TODO
postulate ⇒-trans : ∀ {n} {A B C : Formula n} → ⊨ A ⇒ B → ⊨ B ⇒ C → ⊨ A ⇒ C
postulate ⊨A∸x⇒B : ∀ {n} (A B : Formula n) x → ⊨ A ⇒ B → ⊨ A ∸ x ⇒ B
