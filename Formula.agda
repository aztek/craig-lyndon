module Formula where

open import Data.Fin
open import Data.Fin.Props
open import Data.Fin.Subset
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Vec
open import Data.Bool as Bool using (Bool) renaming (_∧_ to ⋀; _∨_ to ⋁)
open import Relation.Nullary using (yes; no)
open import Function

Var = Fin

infixl 5 _⇒_
data Formula (n : ℕ) : Set where
  true false : Formula n
  var : (x : Var n) → Formula n
  !_  : (f : Formula n) → Formula n
  _∧_ _∨_ _⇒_ : (f g : Formula n) → Formula n

Interpretation = Vec Bool

_⟪_⟫_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        (A → B) → (B → C → D) → (A → C) → A → D
f ⟪ _*_ ⟫ g = λ x → f x * g x

eval : ∀ {n} → Formula n → Interpretation n → Bool
eval true    = const Bool.true
eval false   = const Bool.false
eval (var x) = lookup x
eval (! f)   = Bool.not ∘ eval f
eval (f ∧ g) = eval f ⟪ ⋀ ⟫ eval g
eval (f ∨ g) = eval f ⟪ ⋁ ⟫ eval g
eval (f ⇒ g) = (Bool.not ∘ eval f) ⟪ ⋁ ⟫ eval g

Model : ∀ {n} → Formula n → Interpretation n → Set
Model f = Bool.T ∘ eval f

infixl 4 ⊨_
⊨_ : ∀ {n} → Formula n → Set
⊨ f = ∃ (Model f)

atoms : ∀ {n} → Formula n → Subset n
atoms (var x) = ⁅ x ⁆
atoms (! f)   = atoms f
atoms (f ∧ g) = atoms f ∪ atoms g
atoms (f ∨ g) = atoms f ∪ atoms g
atoms (f ⇒ g) = atoms f ∪ atoms g
atoms const   = replicate outside

_[_/_] : ∀ {n} → Formula n → Var n → Formula n → Formula n
(var x) [ y / C ]
  with x ≟ y
...  | yes _ = C
...  | no  _ = var x
(! A) [ x / C ] = ! A [ x / C ]
(A ∧ B) [ x / C ] = A [ x / C ] ∧ B [ x / C ]
(A ∨ B) [ x / C ] = A [ x / C ] ∨ B [ x / C ]
(A ⇒ B) [ x / C ] = A [ x / C ] ⇒ B [ x / C ]
const [ _ / _ ] = const

infixl 6 _∸_
_∸_ : ∀ {n} (A : Formula n) (x : Var n) → Formula n
A ∸ x = A [ x / true ] ∨ A [ x / false ]

data Connective {n : ℕ} : (Formula n → Formula n → Formula n) → Set where
  or   : Connective _∨_
  and  : Connective _∧_
  impl : Connective _⇒_

data Constant {n : ℕ} : Formula n → Set where
  true  : Constant true
  false : Constant false
