module fib where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Function
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; subst; cong; sym)
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

data Inspect {A : Set}(x : A) : Set where
  _with-≡_ : (y : A) → x ≡ y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = x with-≡ refl

step-even : ∀ n → IsEven n → IsEven (suc (suc n))
step-even n p with parity n
step-even .(k * 2) tt | even k = tt
step-even .(suc (k * 2)) () | odd k

pets-even : ∀ n → IsEven (suc (suc n)) → IsEven n
pets-even n p with parity n
pets-even .(k * 2) p | even k = tt
pets-even .(suc (k * 2)) () | odd k

step-odd : ∀ n → IsOdd n → IsOdd (suc (suc n))
step-odd n p with parity n
step-odd .(k * 2) () | even k
step-odd .(suc (k * 2)) tt | odd k = tt

pets-odd : ∀ n → IsOdd (suc (suc n)) → IsOdd n
pets-odd n p with parity n
pets-odd .(k * 2) () | even k
pets-odd .(suc (k * 2)) tt | odd k = tt

trivEven : ∀ k → IsEven (k * 2)
trivEven zero = tt
trivEven (suc zero) = tt
trivEven (suc (suc k)) = step-even (suc (suc (k * 2))) (trivEven (suc k))

trivOdd : ∀ k → IsOdd (1 + k * 2)
trivOdd zero = tt
trivOdd (suc zero) = tt
trivOdd (suc (suc k)) = step-odd (suc (suc (suc (k * 2)))) (trivOdd (suc k))

triv¬Even : ∀ k → ¬ IsEven (1 + k * 2)
triv¬Even zero = id
triv¬Even (suc k) = odd→¬even (suc (suc (suc (k * 2)))) (step-odd (suc (k * 2)) (trivOdd k))

triv¬Odd : ∀ k → ¬ IsOdd (k * 2)
triv¬Odd zero = id
triv¬Odd (suc k) = even→¬odd (suc (suc (k * 2))) (step-even (k * 2) (trivEven k))

next-even-is-odd : ∀ n → IsEven n → IsOdd (suc n)
next-even-is-odd n p with parity n
next-even-is-odd .(k * 2) tt | even k = trivOdd k
next-even-is-odd .(suc (k * 2)) () | odd k

prev-even-is-odd : ∀ n → IsEven (suc n) → IsOdd n
prev-even-is-odd n p with parity n
prev-even-is-odd .(k * 2) p | even k = triv¬Even k p
prev-even-is-odd .(suc (k * 2)) p | odd k = tt

next-odd-is-even : ∀ n → IsOdd n → IsEven (suc n)
next-odd-is-even n p with parity n
next-odd-is-even .(k * 2) () | even k
next-odd-is-even .(suc (k * 2)) tt | odd k = step-even (k * 2) (trivEven k)

even-comm : ∀ m n → IsEven (m + n) → IsEven (n + m)
even-comm m n p = lemma IsEven (+-comm m n) p

odd-comm : ∀ m n → IsOdd (m + n) → IsOdd (n + m)
odd-comm m n p = lemma IsOdd (+-comm m n) p

even+even=even : ∀ m n → IsEven m → IsEven n → IsEven (m + n)
even+even=even zero zero p q = tt
even+even=even zero (suc n) p q = q
even+even=even (suc m) zero p tt = lemma IsEven (1+m≡1+[m+0] m) p
even+even=even (suc zero) (suc zero) p q = tt
even+even=even (suc zero) (suc (suc n)) () q
even+even=even (suc (suc m)) (suc zero) p ()
even+even=even (suc (suc m)) (suc (suc n)) p q
  = step-even (m + suc (suc n)) (even+even=even m (suc (suc n)) (pets-even m p) q)

odd+odd=even : ∀ m n → IsOdd m → IsOdd n → IsEven (m + n)
odd+odd=even zero zero () q
odd+odd=even zero (suc n) () q
odd+odd=even (suc m) zero p ()
odd+odd=even (suc zero) (suc zero) tt tt = tt
odd+odd=even (suc zero) (suc (suc n)) tt q = next-odd-is-even (suc (suc n)) q
odd+odd=even (suc (suc m)) (suc zero) p tt
  = next-odd-is-even (suc (m + 1)) (lemma IsOdd (cong suc (+-comm 1 m)) p)
odd+odd=even (suc (suc m)) (suc (suc n)) p q
  = step-even (m + suc (suc n)) (odd+odd=even m (suc (suc n)) (pets-odd m p) q)

odd+even=odd : ∀ m n → IsOdd m → IsEven n → IsOdd (m + n)
odd+even=odd zero zero () q
odd+even=odd zero (suc n) () q
odd+even=odd (suc m) zero p tt = lemma IsOdd (1+m≡1+[m+0] m) p
odd+even=odd (suc zero) (suc zero) p ()
odd+even=odd (suc zero) (suc (suc n)) tt q = next-even-is-odd (suc (suc n)) q
odd+even=odd (suc (suc m)) (suc zero) p ()
odd+even=odd (suc (suc m)) (suc (suc n)) p q
  = step-odd (m + suc (suc n)) (odd+even=odd m (suc (suc n)) (pets-odd m p) q)

