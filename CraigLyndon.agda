open import Data.Nat

-- The proof is parametrized by the number of variables in the domain
module CraigLyndon (n : ℕ) where

open import Function using (_∘_; _$_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Subset
open import Data.Empty
open import Data.Fin.Subset.Props
open import Data.Sum renaming (_⊎_ to _⋁_)
open import Data.Product renaming (_×_ to _⋀_)
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
data ⊨_ (f : Formula) : Set where
  model : ∃ (Model f) → ⊨ f

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

⊆-− : ∀ {m} (α* β* : Subset m) {x} → x ∈ α* − β* → x ∈ α*
⊆-− [] [] ()
⊆-− (inside  ∷ α*) (outside ∷ β*) here = here
⊆-− (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = there (⊆-− α* β* x∈α*−β*)
⊆-− (inside  ∷ α*) (inside  ∷ β*) (there x∈α*−β*) = there (⊆-− α* β* x∈α*−β*)
⊆-− (outside ∷ α*) (_       ∷ β*) (there x∈α*−β*) = there (⊆-− α* β* x∈α*−β*)

⊈-− : ∀ {m} (α* β* : Subset m) {x} → x ∈ α* − β* → x ∉ β*
⊈-− [] [] ()
⊈-− (inside  ∷ α*) (outside ∷ β*) here = λ ()
⊈-− (inside  ∷ α*) (outside ∷ β*) (there x∈α*−β*) = ⊈-− α* β* x∈α*−β* ∘ drop-there
⊈-− (inside  ∷ α*) (inside  ∷ β*) {zero} ()
⊈-− (inside  ∷ α*) (inside  ∷ β*) {suc _} (there x∈α*−β*) = ⊈-− α* β* x∈α*−β* ∘ drop-there
⊈-− (outside ∷ α*) (_       ∷ β*) {zero} ()
⊈-− (outside ∷ α*) (_       ∷ β*) {suc _} (there x∈α*−β*) = ⊈-− α* β* x∈α*−β* ∘ drop-there

drop-suc : ∀ m n → suc m ≤′ suc n → m ≤′ n
drop-suc zero zero s = ≤′-refl
drop-suc zero (suc n₁) (≤′-step s) = ≤′-step (drop-suc zero n₁ s)
drop-suc (suc m) zero (≤′-step ())
drop-suc (suc .n₁) (suc n₁) ≤′-refl = ≤′-refl
drop-suc (suc m) (suc n₁) (≤′-step s) = ≤′-step (drop-suc (suc m) n₁ s)

fromℕ≤′ : ∀ m n → m <′ n → Fin n
fromℕ≤′ _ zero ()
fromℕ≤′ zero (suc n) _ = zero
fromℕ≤′ (suc m) (suc n) m<′n = suc (fromℕ≤′ m n (drop-suc (suc m) n m<′n))

drop-suc₂ : ∀ m n → suc m ≤′ n → m ≤′ n
drop-suc₂ zero zero ()
drop-suc₂ zero (suc .0) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ zero (suc n₁) (≤′-step s) = ≤′-step (drop-suc₂ zero n₁ s)
drop-suc₂ (suc m) zero ()
drop-suc₂ (suc m) (suc .(suc m)) ≤′-refl = ≤′-step ≤′-refl
drop-suc₂ (suc m) (suc n₁) (≤′-step s) = ≤′-step (drop-suc₂ (suc m) n₁ s)

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

data ∣_−_∣ {n} (α* β* : Subset n) : Set where
  []  : ∀ {x} → x ∈ α* → x ∈ β* → ∣ α* − β* ∣
  _∷_ : ∀ {x} → x ∈ α* → x ∉ β* → ∣ α* [ x ]≔ outside − β* ∣ → ∣ α* − β* ∣

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

find-interpolant : (φ ψ : Formula) → Formula
find-interpolant φ ψ
  with induction (atoms φ − atoms ψ)
...  | [] _ = φ
...  | _∷_ {x} x∈d i = {!!}
{-
  with ∃-diff (atoms φ) (atoms ψ) e
...  | ρ , ρ∈xs , ρ∉ys = let φ′ : Formula
                             φ′ = φ [ ρ / true ] ∨ φ [ ρ / false ]
                          in {!!}
-}

module Properties (φ ψ : Formula)
                  (⊨φ⇒ψ : ⊨ φ ⇒ ψ) where
  private
    tautology : ∀ {χ} → ⊨ χ ⇒ χ
    tautology {χ} = model (i , helper χ)
      where
        i : Interpretation
        i = replicate Bool.true

        helper : ∀ f → Model (f ⇒ f) i
        helper f
          with eval f i
        ...  | Bool.true  = tt
        ...  | Bool.false = tt

  ρ = find-interpolant φ ψ

  interpolates-φ : ⊨ φ ⇒ ρ
  interpolates-φ
    with induction (atoms φ − atoms ψ)
  ...  | [] e = tautology
  ...  | x ∷ i = {!!}

  interpolates-ψ : ⊨ ρ ⇒ ψ
  interpolates-ψ
    with induction (atoms φ − atoms ψ)
  ...  | [] e  = ⊨φ⇒ψ
  ...  | x ∷ i = {!!}

  private
    diff-⊆ : ∀ {n} {xs ys : Subset n} → Empty (xs − ys) → xs ⊆ ys
    diff-⊆ {n} {xs} {ys} p {x} = helper xs ys p x
      where
        helper : ∀ {m} (xs ys : Subset m) → Empty (xs − ys) →
                 ∀ α → α ∈ xs → α ∈ ys
        helper [] [] _ _ ()
        helper (inside  ∷ xs) (inside  ∷ ys) _ zero _ = here
        helper (inside  ∷ xs) (inside  ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (λ { (x , s) → e (suc x , there s) }) α α∈xs)
        helper (inside  ∷ xs) (outside ∷ ys) e zero here = ⊥-elim (e (zero , here))
        helper (inside  ∷ xs) (outside ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (λ _ → e (zero , here)) α α∈xs)
        helper (outside ∷ xs) (_       ∷ ys) e zero ()
        helper (outside ∷ xs) (_       ∷ ys) e (suc α) (there α∈xs) = there (helper xs ys (λ { (x , s) → e (suc x , there s) }) α α∈xs)

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

    encloses-own-atoms : ∀ {xs ys : Atoms} → Empty (xs − ys) → xs ⊆ xs ∩ ys
    encloses-own-atoms = ⊆-intersection ∘ diff-⊆

  encloses-atoms : atoms ρ ⊆ atoms φ ∩ atoms ψ
  encloses-atoms
    with induction (atoms φ − atoms ψ)
  ...  | [] e = encloses-own-atoms e
  ...  | x ∷ i = {!!}

  craig-lyndon : (atoms ρ ⊆ atoms φ ∩ atoms ψ) ⋀ (⊨ φ ⇒ ρ) ⋀ (⊨ ρ ⇒ ψ)
  craig-lyndon = encloses-atoms , interpolates-φ , interpolates-ψ
