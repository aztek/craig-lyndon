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

postulate
  ∸-∉ : ∀ {n} (A : Formula n) x → x ∉ atoms (A ∸ x)
--∸-∉ A x = ∉-map _∨_ (A [ x / true ]) (A [ x / false ]) x or (∉-replace-true A x) (∉-replace-false A x)

--q : ∀ {n} {A : Formula n} x y → x ∈ atoms A → x ∈ atoms (A ∸ y) ⇔ ¬ (x ≡ y)
--q = ?

{-
[/]-equisat : ∀ {n} (φ : Formula n) {ρ} → ⊨ φ → ⊨ φ [ ρ / true ] ∨ φ [ ρ / false ]
[/]-equisat φ {ρ} (i , model)
  with lookup ρ i
...  | Bool.true = {!!}
...  | Bool.false = {!!}

[/]-equisat true  (i , model) = i , Unit.tt
[/]-equisat false (i , model) = i , model
[/]-equisat (var x) {ρ} (i , model)
  with toℕ x ≟ toℕ ρ
...  | yes _ = i , Unit.tt
...  | no  _ = i , {!!}
[/]-equisat (! φ) (i , model) = {!!}
[/]-equisat (φ ∧ ψ) (i , model) = {!!}
[/]-equisat (φ ∨ ψ) (i , model) = {!!}
[/]-equisat (φ ⇒ ψ) (i , model) = {!!}
-}
-- TODO
postulate ∸-⇒ : ∀ {n} {A B : Formula n} {x} → ⊨ A ⇒ B → ⊨ A ∸ x ⇒ B
{-[/]-⇒ true  = replicate outside , Unit.tt
[/]-⇒ false = replicate outside , Unit.tt
[/]-⇒ (var x) {ρ}
  with toℕ x ≟ toℕ ρ
...  | yes _ = (replicate outside) , {!!}
...  | no  _ = {!!}
[/]-⇒ (! φ) {ρ}
  with [/]-⇒ φ {ρ}
...  | i , model = i , {!!} 
[/]-⇒ (φ ∧ ψ) = {!!}
[/]-⇒ (φ ∨ ψ) = {!!}
[/]-⇒ (φ ⇒ ψ) = {!!}
-}
-- TODO
postulate ⇒-trans : ∀ {n} {A B C : Formula n} → ⊨ A ⇒ B → ⊨ B ⇒ C → ⊨ A ⇒ C
{-⇒-trans {n} {φ} {ρ} {ψ} (x , proj₂) (y , proj₄)
  with eval φ x   | inspect (eval φ) x
...  | Bool.true  | [ e ] = x , {!!}
...  | Bool.false | [ e ] rewrite e = {!!} , {!!}
-}

--postulate ∸-atoms : ∀ {n} {A : Formula n} {x} → atoms (A ∸ x) ≡ atoms A − ⁅ x ⁆

solve₁ : ∀ {p : Bool → Bool} (x : Bool)
         {t : T (p B.true)}
         {f : T (p B.false)}
         → T (p x)
solve₁ B.true  = λ {t} {_} → t
solve₁ B.false = λ {_} {f} → f

solve₂ : ∀ {f : Bool → Bool → Bool} (x y : Bool)
         {_ : T (f B.true  B.true)}
         {_ : T (f B.true  B.false)}
         {_ : T (f B.false B.true)}
         {_ : T (f B.false B.false)}
         → T (f x y)
solve₂ B.true  B.true  = λ {z} {_} {_} {_} → z
solve₂ B.true  B.false = λ {_} {z} {_} {_} → z
solve₂ B.false B.true  = λ {_} {_} {z} {_} → z
solve₂ B.false B.false = λ {_} {_} {_} {z} → z

solve₃ : ∀ {f : Bool → Bool → Bool → Bool}
         (x y z : Bool)
         {ttt : T (f B.true  B.true  B.true )}
         {ttf : T (f B.true  B.true  B.false)}
         {tft : T (f B.true  B.false B.true )}
         {tff : T (f B.true  B.false B.false)}
         {ftt : T (f B.false B.true  B.true )}
         {ftf : T (f B.false B.true  B.false)}
         {fft : T (f B.false B.false B.true )}
         {fff : T (f B.false B.false B.false)}
         → T (f x y z)
solve₃ B.true  B.true  B.true  = λ {z} {_} {_} {_} {_} {_} {_} {_} → z
solve₃ B.true  B.true  B.false = λ {_} {z} {_} {_} {_} {_} {_} {_} → z
solve₃ B.true  B.false B.true  = λ {_} {_} {z} {_} {_} {_} {_} {_} → z
solve₃ B.true  B.false B.false = λ {_} {_} {_} {z} {_} {_} {_} {_} → z
solve₃ B.false B.true  B.true  = λ {_} {_} {_} {_} {z} {_} {_} {_} → z
solve₃ B.false B.true  B.false = λ {_} {_} {_} {_} {_} {z} {_} {_} → z
solve₃ B.false B.false B.true  = λ {_} {_} {_} {_} {_} {_} {z} {_} → z
solve₃ B.false B.false B.false = λ {_} {_} {_} {_} {_} {_} {_} {z} → z

tautology : ∀ {n} (A : Formula n) → ⊨ A ⇒ A
tautology A = i , model
  where
    i = replicate B.true
    model = solve₁ {λ x → ¬♭ x ∨♭ x} (eval A i)

postulate ⊨A⇒A∸x : ∀ {n} (A : Formula n) (x : Var n) → ⊨ A ⇒ A ∸ x

--∸⇔∉ : ∀ {n} {A : Formula n} {x} {y} → x ∉ atoms (A ∸ x) 
