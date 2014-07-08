open import Data.Nat

module Formula where

open import Relation.Nullary
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Function
open import Data.Product as Product renaming (_×_ to _⋀_)
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

atoms : ∀ {n} → Formula n → Subset n
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

data Constant {n : ℕ} : Formula n → Set where
  true  : Constant true
  false : Constant false
