module fib where

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

