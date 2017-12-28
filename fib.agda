module fib where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Nat
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

toFib : (n : ℕ) → Fib n (fib n)
toFib zero = Fib0
toFib (suc zero) = Fib1
toFib (suc (suc n)) = FibN (toFib (suc n)) (toFib n)

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc zero) = odd zero
parity (suc (suc n)) with parity n
... | even k = even (suc k)
... | odd  k  = odd (suc k)

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(suc (k * 2)) | odd k = k

even? : ℕ → Bool
even? n with parity n
even? .(k * 2) | even k = true
even? .(suc (k * 2)) | odd k = false

odd? : ℕ → Bool
odd? n with parity n
odd? .(k * 2) | even k = false
odd? .(suc (k * 2)) | odd k = true

isTrue : Bool → Set
isTrue false = ⊥
isTrue true = ⊤

isFalse : Bool → Set
isFalse false = ⊥
isFalse true = ⊤
