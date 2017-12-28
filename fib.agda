module fib where

open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; subst)

data Fib : ℕ → ℕ → Set where
  Fib0 : Fib 0 1
  Fib1 : Fib 1 1
  FibN : ∀ {n x y} → Fib (suc n) x → Fib n y → Fib (suc (suc n)) (x + y)

FibFunc : (ℕ → ℕ) → Set
FibFunc f = ∀ n → Fib n (f n)

fib : ℕ → ℕ
fib (suc (suc n)) = fib (suc n) + fib n
fib n = 1

-- To prove fib is FibFunc
fib-is-FibFunc : FibFunc fib
fib-is-FibFunc zero = Fib0
fib-is-FibFunc (suc zero) = Fib1
fib-is-FibFunc (suc (suc n)) = FibN (fib-is-FibFunc (suc n)) (fib-is-FibFunc n)

view : (n : ℕ) → Fib n (fib n)
view zero = Fib0
view (suc zero) = Fib1
view (suc (suc n)) = FibN (view (suc n)) (view n)

-- momoko-hypothesis-1
triv : ∀ n → fib (suc (suc n)) ≡ fib (suc n) + fib n
triv n = refl

lemma0 : ∀ n → fib (n * 3) mod 2 ≡ fsuc fzero
lemma0 zero = refl
lemma0 (suc zero) = refl
lemma0 (suc (suc n)) = {!!}

lemma1 : ∀ n → fib (1 + n * 3) mod 2 ≡ fsuc fzero
lemma1 = {!!}

momoko1 : ∀ n → fib (2 + n * 3) mod 2 ≡ fzero
momoko1 zero = refl
momoko1 (suc zero) = refl
momoko1 (suc (suc n)) with lemma0 n | lemma1 (suc n)
... | p | q = {!!}
