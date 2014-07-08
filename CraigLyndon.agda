open import Data.Nat

-- The proof is parametrized by the number of variables in the domain
module CraigLyndon (n : ℕ) where

open import Function using (_∘_; _$_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Function
open import Data.Empty
open import Data.Fin.Subset.Props
open import Data.Sum renaming (_⊎_ to _⋁_)
open import Data.Product as Product renaming (_×_ to _⋀_)
open import Data.Unit hiding (_≟_; _≤_)
open import Data.Vec as Vec hiding ([_]; _∈_)
open import Data.Bool as Bool using (Bool; T; if_then_else_)
                      renaming (_∧_ to _∧♭_; _∨_ to _∨♭_; not to ¬♭_)

Var = Fin n

data Formula : Set where
  true false : Formula
  var : (x : Var) → Formula
  !_  : (f : Formula) → Formula
  _∧_ _∨_ _⇒_ : (f g : Formula) → Formula

Interpretation = Vec Bool n

eval : Formula → Interpretation → Bool
eval true  i = Bool.true
eval false i = Bool.false
eval (var x) i = lookup x i
eval (! f)   i = ¬♭ eval f i
eval (f ∧ g) i = eval f i ∧♭ eval g i
eval (f ∨ g) i = eval f i ∨♭ eval g i
eval (f ⇒ g) i = (¬♭ eval f i) ∨♭ eval g i

Model : Formula → Interpretation → Set
Model f i = T (eval f i)

infixl 5 ⊨_
⊨_ : Formula → Set
⊨ f = ∃ (Model f)

Atoms = Subset n

replicate-all : {A : Set} {a : A} {m : ℕ} (x : Fin m) → replicate a [ x ]= a
replicate-all zero = here
replicate-all (suc x) = there (replicate-all x)

outside-∉ : ∀ {n} {x} {p : Subset n} → p [ x ]= outside → x ∉ p
outside-∉ here ()
outside-∉ (there x∉p) (there x∈p) = outside-∉ x∉p x∈p

∅ : ∀ {n} → Subset n
∅ = replicate outside

Empty-∅ : ∀ {n} → Empty {n} ∅
Empty-∅ (x , x∈∅) = outside-∉ (replicate-all x) x∈∅

atoms : Formula → Atoms
atoms (var x) = ⁅ x ⁆
atoms (! f)   = atoms f
atoms (f ∧ g) = atoms f ∪ atoms g
atoms (f ∨ g) = atoms f ∪ atoms g
atoms (f ⇒ g) = atoms f ∪ atoms g
atoms const   = ∅

_−_ : ∀ {m} → Subset m → Subset m → Subset m
[] − [] = []
(inside ∷ α*) − (outside ∷ β*) = inside  ∷ (α* − β*)
(_      ∷ α*) − (_       ∷ β*) = outside ∷ (α* − β*)

⊆-diff : ∀ {m} (α* β* : Subset m) {x} → x ∈ α* − β* → x ∈ α*
⊆-diff [] [] ()
⊆-diff (inside  ∷ α*) (outside ∷ β*) here = here
⊆-diff (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)
⊆-diff (inside  ∷ α*) (inside  ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)
⊆-diff (outside ∷ α*) (_       ∷ β*) (there x∈α*−β*) = there (⊆-diff α* β* x∈α*−β*)

⊈-diff : ∀ {m} (α* β* : Subset m) {x} → x ∈ α* − β* → x ∉ β*
⊈-diff [] [] ()
⊈-diff (inside  ∷ α*) (outside ∷ β*) here = λ ()
⊈-diff (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there
⊈-diff (inside  ∷ α*) (inside  ∷ β*) {zero} ()
⊈-diff (inside  ∷ α*) (inside  ∷ β*) {suc _} (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there
⊈-diff (outside ∷ α*) (_       ∷ β*) {zero} ()
⊈-diff (outside ∷ α*) (_       ∷ β*) {suc _} (there x∈α*−β*) = ⊈-diff α* β* x∈α*−β* ∘ drop-there

drop-suc : ∀ m n → suc m ≤′ suc n → m ≤′ n
drop-suc zero zero s = ≤′-refl
drop-suc zero (suc n) (≤′-step s) = ≤′-step (drop-suc zero n s)
drop-suc (suc m) zero (≤′-step ())
drop-suc (suc .n) (suc n) ≤′-refl = ≤′-refl
drop-suc (suc m) (suc n) (≤′-step s) = ≤′-step (drop-suc (suc m) n s)

fromℕ≤′ : ∀ m n → m <′ n → Fin n
fromℕ≤′ _ zero ()
fromℕ≤′ zero (suc n) _ = zero
fromℕ≤′ (suc m) (suc n) m<′n = suc (fromℕ≤′ m n (drop-suc (suc m) n m<′n))

drop-suc₂ : ∀ m n → suc m ≤′ n → m ≤′ n
drop-suc₂ zero zero ()
drop-suc₂ zero (suc .0) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ zero (suc n) (≤′-step s) = ≤′-step (drop-suc₂ zero n s)
drop-suc₂ (suc m) zero ()
drop-suc₂ (suc m) (suc .(suc m)) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ (suc m) (suc n) (≤′-step s) = ≤′-step (drop-suc₂ (suc m) n s)

open import Data.List using (List; []; _∷_)

iterate : (α* : Subset n) → List (Fin n)
iterate α* = helper {n} {≤′-refl} α*
  where helper : {m : ℕ} {m≤′n : m ≤′ n} → Subset m → List (Fin n)
        helper [] = []
        helper {suc m} {m<n} (inside  ∷ α*) = fromℕ≤′ m n m<n ∷ helper {m} {drop-suc₂ m n m<n} α*
        helper {suc m} {m<n} (outside ∷ α*) = helper {m} {drop-suc₂ m n m<n} α*

-- Induction over the subset
data Induction {n} (p : Subset n) : Set where
  []  : Empty p → Induction p
  _∷_ : ∀ {x} → x ∈ p → Induction (p [ x ]≔ outside) → Induction p

induction : (α* : Subset n) → Induction α*
induction α* = helper {n} {≤′-refl} ∅ ([] Empty-∅) α*
  where Empty-outside : ∀ {n} {p : Subset n} → Empty p → Empty (outside ∷ p)
        Empty-outside _ (zero , ())
        Empty-outside e (suc x , there x∈p) = e (x , x∈p)

        ∷-induction : ∀ {n} (p : Subset n) → Induction p → Induction (outside ∷ p)
        ∷-induction p ([] e) = [] (Empty-outside e)
        ∷-induction p (_∷_ {x} x∈p i) = there x∈p ∷ ∷-induction (p [ x ]≔ outside) i

        helper : {m : ℕ} {m≤n : m ≤′ n} (acc : Subset n) (ind-acc : Induction acc) (β* : Subset m) → Induction β*
        helper {zero}  {0<n} _ _ [] = [] (λ { (_ , ()) })
        helper {suc m} {m<n} a i (inside  ∷ p) = here ∷ ∷-induction p (helper {m} {drop-suc₂ m n m<n} a i p)
        helper {suc m} {m<n} a i (outside ∷ p) = ∷-induction p (helper {m} {drop-suc₂ m n m<n} a i p)

_[_/_] : Formula → Var → Formula → Formula
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

data Connective : (Formula → Formula → Formula) → Set where
  or   : Connective _∨_
  and  : Connective _∧_
  impl : Connective _⇒_

∉-map : ∀ _⊕_ φ ψ ρ → Connective _⊕_ → ρ ∉ atoms φ → ρ ∉ atoms ψ → ρ ∉ atoms (φ ⊕ ψ)
∉-map φ ψ ρ ρ∉φ ρ∉ψ ρ∈φ∨ψ = {!!}

data Constant : Formula → Set where
  true  : Constant true
  false : Constant false

∉-replace-true : ∀ φ ρ → ρ ∉ atoms (φ [ ρ / true ])
∉-replace-true true  ρ = outside-∉ (replicate-all ρ)
∉-replace-true false ρ = outside-∉ (replicate-all ρ)
∉-replace-true (var x) ρ
  with toℕ x ≟ toℕ ρ
...  | yes _ = outside-∉ (replicate-all ρ)
...  | no  ρ≠x = {!outside-∉ (replicate-all ρ)!}
∉-replace-true (! φ) ρ = ∉-replace-true φ ρ
∉-replace-true (φ ∧ ψ) ρ = ∉-map _∧_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ and  (∉-replace-true φ ρ) (∉-replace-true ψ ρ)
∉-replace-true (φ ∨ ψ) ρ = ∉-map _∨_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ or   (∉-replace-true φ ρ) (∉-replace-true ψ ρ)
∉-replace-true (φ ⇒ ψ) ρ = ∉-map _⇒_ (φ [ ρ / true ]) (ψ [ ρ / true ]) ρ impl (∉-replace-true φ ρ) (∉-replace-true ψ ρ)

∉-replace-false : ∀ {φ ρ} → ρ ∉ atoms (φ [ ρ / false ])
∉-replace-false = {!!}

subst-replaces : ∀ {φ ρ} → ρ ∉ atoms (φ [ ρ / true ] ∨ φ [ ρ / false ])
subst-replaces {φ} {ρ} = ∉-map _∨_ (φ [ ρ / true ]) (φ [ ρ / false ]) ρ or (∉-replace-true φ ρ) (∉-replace-false {φ} {ρ})

find-interpolant : (φ ψ : Formula) → Formula
find-interpolant φ ψ = helper (induction (atoms φ − atoms ψ))
  where
    helper : Induction (atoms φ − atoms ψ) → Formula
    helper ([] _) = φ
    helper (_∷_ {ρ} ρ∈d α*)
      with ⊆-diff (atoms φ) (atoms ψ) ρ∈d | ⊈-diff (atoms φ) (atoms ψ) ρ∈d
    ...  | ρ∈atoms[φ]                     | ρ∉atoms[ψ]
      with φ [ ρ / true ] ∨ φ [ ρ / false ]
    ...  | φ′ = let ⊨φ′⇒ψ : ⊨ φ′ ⇒ ψ
                    ⊨φ′⇒ψ = {!!}
                    ⊨φ⇒φ′ : ⊨ φ ⇒ φ′
                    ⊨φ⇒φ′ = {!!}
                 in {!!}

⇒-trans : ∀ {φ ρ ψ} → ⊨ φ ⇒ ρ → ⊨ ρ ⇒ ψ → ⊨ φ ⇒ ψ
⇒-trans {φ} {ρ} {ψ} (x , proj₂) (y , proj₄)
  with eval φ x
...  | Bool.true  = x , {!!}
...  | Bool.false = {!!}

private
  tautology : ∀ {χ} → ⊨ χ ⇒ χ
  tautology {χ} = i , helper χ
    where
      i : Interpretation
      i = replicate Bool.true

      helper : ∀ f → Model (f ⇒ f) i
      helper f
        with eval f i
      ...  | Bool.true  = tt
      ...  | Bool.false = tt

private
  diff-⊆ : ∀ {n} {xs ys : Subset n} → Empty (xs − ys) → xs ⊆ ys
  diff-⊆ {n} {xs} {ys} p {x} = helper xs ys p x
    where
      helper : ∀ {m} (xs ys : Subset m) → Empty (xs − ys) →
               ∀ α → α ∈ xs → α ∈ ys
      helper [] [] _ _ ()
      helper (inside  ∷ xs) (inside  ∷ ys) _ zero _ = here
      helper (inside  ∷ xs) (inside  ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ Product.map suc there) α α∈xs)
      helper (inside  ∷ xs) (outside ∷ ys) e zero here = ⊥-elim $ e (zero , here)
      helper (inside  ∷ xs) (outside ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ const (zero , here)) α α∈xs)
      helper (outside ∷ xs) (_       ∷ ys) e zero ()
      helper (outside ∷ xs) (_       ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (e ∘ Product.map suc there) α α∈xs)

  ⊆-itself : ∀ {n} {xs : Subset n} → xs ⊆ xs
  ⊆-itself = λ {_} {_} {_} z → z

  ⊆-intersection : ∀ {n} {xs ys : Subset n} → xs ⊆ ys → xs ⊆ xs ∩ ys
  ⊆-intersection {zero}  {[]} {[]} _ = λ z → z
  ⊆-intersection {suc n} {x ∷ xs} {y ∷ ys} xs⊆ys = helper
    where
      open import Relation.Binary.PropositionalEquality

      drop-here : ∀ {n} {s} {p : Subset n} → zero ∈ s ∷ p → s ≡ inside
      drop-here here = refl

      helper : x ∷ xs ⊆ (x ∷ xs) ∩ (y ∷ ys)
      helper {zero}  z∈i rewrite drop-here z∈i | drop-here (xs⊆ys z∈i) = here
      helper {suc z} s∈i = there (⊆-intersection (drop-there ∘ xs⊆ys ∘ there) (drop-there s∈i))

  encloses-own-atoms : ∀ {n} {xs ys : Subset n} → Empty (xs − ys) → xs ⊆ xs ∩ ys
  encloses-own-atoms = ⊆-intersection ∘ diff-⊆

  ⊆-distrib-∩ : ∀ {n} {xs xs′ ys : Subset n} → xs ⊆ xs′ → xs ∩ ys ⊆ xs′ ∩ ys
  ⊆-distrib-∩ = {!!}

  ⊆-trans : ∀ {n} {xs ys zs : Subset n} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans = {!!}

interpolate : ∀ φ ψ → ⊨ φ ⇒ ψ → ∃ λ ρ → (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
interpolate φ ψ = helper φ ψ (induction $ atoms φ − atoms ψ)
  where helper : ∀ φ ψ → Induction (atoms φ − atoms ψ) → ⊨ φ ⇒ ψ →
                 ∃ λ ρ → (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
        helper φ ψ ([] e) ⊨φ⇒ψ = φ , encloses-own-atoms e , tautology , ⊨φ⇒ψ
        helper φ ψ (_∷_ {ρ} ρ∈d i) ⊨φ⇒ψ
          with φ [ ρ / true ] ∨ φ [ ρ / false ]
        ...  | φ′ = χ , ⊆-trans χ-atoms (⊆-distrib-∩ φ′-atoms) , ⇒-trans ⊨φ⇒φ′ ⊨φ′⇒χ , ⊨χ⇒ψ
          where hyp : ∃ λ χ → (atoms χ ⊆ atoms φ′ ∩ atoms ψ) ⋀ (⊨ φ′ ⇒ χ) ⋀ (⊨ χ ⇒ ψ)
                hyp = {!!}

                χ : Formula
                χ = proj₁ hyp

                χ-atoms : atoms χ ⊆ atoms φ′ ∩ atoms ψ
                χ-atoms = proj₁ (proj₂ hyp)

                ⊨φ′⇒χ : ⊨ φ′ ⇒ ψ
                ⊨φ′⇒χ = proj₁ (proj₂ (proj₂ hyp))

                ⊨χ⇒ψ : ⊨ χ ⇒ ψ
                ⊨χ⇒ψ = proj₂ (proj₂ (proj₂ hyp))

                ⊨φ⇒φ′ : ⊨ φ ⇒ φ′
                ⊨φ⇒φ′ = {!!}

                φ′-atoms : atoms φ′ ⊆ atoms φ
                φ′-atoms = {!!}

