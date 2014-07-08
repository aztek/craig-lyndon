open import Data.Nat
open import Data.Fin.Subset
open import Data.Vec
import Data.Bool as Bool
import Data.Unit as Unit
open import Data.Product as Product renaming (_×_ to _⋀_)

open import Formula

module Formula.Properties where

-- TODO
postulate ∉-map : ∀ {n : ℕ} _⊕_ φ ψ ρ → Connective {n} _⊕_ → ρ ∉ atoms φ → ρ ∉ atoms ψ → ρ ∉ atoms (φ ⊕ ψ)
--∉-map φ ψ ρ ρ∉φ ρ∉ψ ρ∈φ∨ψ = {!!}

-- TODO
postulate ∉-replace-true : ∀ {n} (φ : Formula n) (ρ : Var n) → ρ ∉ atoms (φ [ ρ / true ])
{-∉-replace-true true  ρ = outside-∉ (replicate-all ρ)
∉-replace-true false ρ = outside-∉ (replicate-all ρ)
∉-replace-true (var x) ρ
  with toℕ x ≟ toℕ ρ
...  | yes _   = outside-∉ (replicate-all ρ)
...  | no  ρ≠x = {!outside-∉ (replicate-all ρ)!}
∉-replace-true (! φ) ρ = ∉-replace-true φ ρ
∉-replace-true (φ ∧ ψ) ρ = ∉-map _∧_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ and  (∉-replace-true φ ρ) (∉-replace-true ψ ρ)
∉-replace-true (φ ∨ ψ) ρ = ∉-map _∨_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ or   (∉-replace-true φ ρ) (∉-replace-true ψ ρ)
∉-replace-true (φ ⇒ ψ) ρ = ∉-map _⇒_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ impl (∉-replace-true φ ρ) (∉-replace-true ψ ρ)
-}

-- TODO
postulate ∉-replace-false : ∀ {n} (φ : Formula n) (ρ : Var n) → ρ ∉ atoms (φ [ ρ / false ])
--∉-replace-false = {!!}

subst-replaces : ∀ {n} (φ : Formula n) (ρ : Var n) → ρ ∉ atoms (φ [ ρ / true ] ∨ φ [ ρ / false ])
subst-replaces φ ρ = ∉-map _∨_ (φ [ ρ / true ]) (φ [ ρ / false ]) ρ or (∉-replace-true φ ρ) (∉-replace-false φ ρ)

-- TODO
postulate ⇒-trans : ∀ {n} {φ ρ ψ : Formula n} → ⊨ φ ⇒ ρ → ⊨ ρ ⇒ ψ → ⊨ φ ⇒ ψ
{-⇒-trans {n} {φ} {ρ} {ψ} (x , proj₂) (y , proj₄)
  with eval φ x   | inspect (eval φ) x
...  | Bool.true  | [ e ] = x , {!!}
...  | Bool.false | [ e ] rewrite e = {!!} , {!!}
-}
tautology : ∀ {n} {χ : Formula n} → ⊨ χ ⇒ χ
tautology {n} {χ} = i , model
  where
    i : Interpretation n
    i = replicate Bool.true

    model : Model (χ ⇒ χ) i
    model with eval χ i
    ... | Bool.true  = Unit.tt
    ... | Bool.false = Unit.tt
