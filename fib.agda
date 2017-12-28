module fib where

open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; subst)
open import Relation.Nullary

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

