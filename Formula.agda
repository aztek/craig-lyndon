open import Data.Nat

module Formula where

open import Relation.Nullary
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Function
open import Data.Empty
open import Data.Product as Product renaming (_×_ to _⋀_)
open import Data.Unit as Unit hiding (_≟_; _≤_)
open import Data.Vec as Vec hiding ([_]; _∈_)
open import Data.Bool as Bool using (Bool; T)
                      renaming (_∧_ to _∧♭_; _∨_ to _∨♭_; not to ¬♭_)

open import Subset

Var = Fin

data Formula (n : ℕ) : Set where
  true false : Formula n
  var : (x : Var n) → Formula n
  !_  : (f : Formula n) → Formula n
  _∧_ _∨_ _⇒_ : (f g : Formula n) → Formula n

Interpretation = Vec Bool

eval : ∀ {n} → Formula n → Interpretation n → Bool
eval true  i = Bool.true
eval false i = Bool.false
eval (var x) i = lookup x i
eval (! f)   i = ¬♭ eval f i
eval (f ∧ g) i = eval f i ∧♭ eval g i
eval (f ∨ g) i = eval f i ∨♭ eval g i
eval (f ⇒ g) i = (¬♭ eval f i) ∨♭ eval g i

Model : ∀ {n} → Formula n → Interpretation n → Set
Model f i = T (eval f i)

infixl 5 ⊨_
⊨_ : ∀ {n} → Formula n → Set
⊨ f = ∃ (Model f)

Atoms : {n : ℕ} → Set
Atoms {n} = Subset n

atoms : ∀ {n} → Formula n → Atoms
atoms (var x) = ⁅ x ⁆
atoms (! f)   = atoms f
atoms (f ∧ g) = atoms f ∪ atoms g
atoms (f ∨ g) = atoms f ∪ atoms g
atoms (f ⇒ g) = atoms f ∪ atoms g
atoms const   = ∅

_[_/_] : ∀ {n} → Formula n → Var n → Formula n → Formula n
true  [ _ / _ ] = true
false [ _ / _ ] = false
(var x) [ y / h ]
  with toℕ x ≟ toℕ y
...  | yes _ = h
...  | no  _ = var x
(! f) [ x / h ] = ! f [ x / h ]
(f ∧ g) [ x / h ] = f [ x / h ] ∧ g [ x / h ]
(f ∨ g) [ x / h ] = f [ x / h ] ∨ g [ x / h ]
(f ⇒ g) [ x / h ] = f [ x / h ] ⇒ g [ x / h ]

data Connective {n : ℕ} : (Formula n → Formula n → Formula n) → Set where
  or   : Connective _∨_
  and  : Connective _∧_
  impl : Connective _⇒_

-- TODO
postulate ∉-map : ∀ {n : ℕ} _⊕_ φ ψ ρ → Connective {n} _⊕_ → ρ ∉ atoms φ → ρ ∉ atoms ψ → ρ ∉ atoms (φ ⊕ ψ)
--∉-map φ ψ ρ ρ∉φ ρ∉ψ ρ∈φ∨ψ = {!!}

data Constant {n : ℕ} : Formula n → Set where
  true  : Constant true
  false : Constant false

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
{-⇒-trans {φ} {ρ} {ψ} (x , proj₂) (y , proj₄)
  with eval φ x
...  | Bool.true  = x , {!!}
...  | Bool.false = {!!}
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
