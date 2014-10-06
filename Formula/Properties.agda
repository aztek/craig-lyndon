open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Fin.Subset
open import Data.Vec
open import Data.Fin
open import Data.Bool as B using (Bool; T) renaming (not to ¬♭_; _∨_ to _∨♭_; _∧_ to _∧♭_)
import Data.Unit as Unit
open import Data.Product as Product renaming (_×_ to _⋀_)

open import Formula

module Formula.Properties where

-- TODO
postulate ∸-⇒ : ∀ {n} {A B : Formula n} {x} → ⊨ A ⇒ B → ⊨ A ∸ x ⇒ B

-- TODO
postulate ⇒-trans : ∀ {n} {A B C : Formula n} → ⊨ A ⇒ B → ⊨ B ⇒ C → ⊨ A ⇒ C

-- TODO
postulate ⊨A⇒A∸x : ∀ {n} (A : Formula n) (x : Var n) → ⊨ A ⇒ A ∸ x

solve₁ : ∀ {p : Bool → Bool} (x : Bool)
         {t : T (p B.true)}
         {f : T (p B.false)}
         → T (p x)
solve₁ B.true  = λ {t} {_} → t
solve₁ B.false = λ {_} {f} → f

tautology : ∀ {n} (A : Formula n) → ⊨ A ⇒ A
tautology A = i , model
  where
    i = replicate B.true
    model = solve₁ {λ x → ¬♭ x ∨♭ x} (eval A i)
