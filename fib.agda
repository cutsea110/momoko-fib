module fib where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Nat
-- open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Function
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; subst; cong)
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
half .(1 + k * 2) | odd k = k

even? : ℕ → Bool
even? n with parity n
even? .(k * 2) | even k = true
even? .(1 + k * 2) | odd k = false

odd? : ℕ → Bool
odd? n with parity n
odd? .(k * 2) | even k = false
odd? .(1 + k * 2) | odd k = true

isTrue : Bool → Set
isTrue false = ⊥
isTrue true = ⊤

isFalse : Bool → Set
isFalse false = ⊥
isFalse true = ⊤

IsEven : ℕ → Set
IsEven = isTrue ∘ even?

IsOdd : ℕ → Set
IsOdd = isTrue ∘ odd?

even→¬odd : ∀ n → IsEven n → ¬ IsOdd n
even→¬odd n p with parity n
even→¬odd .(k * 2) p | even k = id
even→¬odd .(1 + k * 2) p | odd k = const p

odd→¬even : ∀ n → IsOdd n → ¬ IsEven n
odd→¬even n p with parity n
odd→¬even .(k * 2) p | even k = const p
odd→¬even .(1 + k * 2) p | odd k = id

lemma : {m n : ℕ} → (P : ℕ → Set) → m ≡ n → P m → P n
lemma P refl q = q

1+m≡1+[m+0] : ∀ m → suc m ≡ suc (m + 0)
1+m≡1+[m+0] zero = refl
1+m≡1+[m+0] (suc m) = cong suc (1+m≡1+[m+0] m)

even+even=even : ∀ m n → IsEven m → IsEven n → IsEven (m + n)
even+even=even zero zero tt tt = tt
even+even=even zero (suc n) tt q = q
even+even=even (suc m) zero p tt = lemma IsEven (1+m≡1+[m+0] m) p
even+even=even (suc m) (suc n) p q = {!!}

odd+odd=even : ∀ m n → IsOdd m → IsOdd n → IsEven (m + n)
odd+odd=even zero zero () q
odd+odd=even zero (suc n) () q
odd+odd=even (suc m) zero p ()
odd+odd=even (suc m) (suc n) p q = {!!}

odd+even=odd : ∀ m n → IsOdd m → IsEven n → IsOdd (m + n)
odd+even=odd zero zero () q
odd+even=odd zero (suc n) () q
odd+even=odd (suc m) zero p tt = lemma IsOdd (1+m≡1+[m+0] m) p
odd+even=odd (suc m) (suc n) p q = {!!}
