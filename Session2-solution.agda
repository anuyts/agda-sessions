{-

|--------------------------------------------------|
| Formal systems and their applications: exercises |
| Session 2: Lists and vectors                     |
|--------------------------------------------------|

-}

-- Part 0: A note on the Agda standard library
--============================================

{-
open import Session1-solution
-}

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat? ; _∸_ to _-_) hiding (pred ; _≤_ ; compare)
open import Relation.Binary.PropositionalEquality
open import Data.Bool renaming (not to ¬)
open import Data.Unit hiding (_≤_)
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)
open import Relation.Nullary hiding (¬_)
is-zero : Nat → Bool
is-zero zero = true
is-zero (suc n) = false


-- Part 1: Lists
--==============

data List (A : Set) : Set where
  [] : List A
  _::_ : (x : A) → (xs : List A) → List A

infixr 15 _::_

example-list : List Nat
example-list = 1 :: 2 :: 3 :: []


length : {A : Set} → List A → Nat
length [] = zero
length (x :: xs) = suc (length xs)

length-test₁ : length {A = Nat} [] ≡ 0
length-test₁ = refl

length-test₂ : length example-list ≡ 3
length-test₂ = refl

-- First, try to explain why we cannot define a head function of type
-- `{A : Set} → List A →  A`.

-- ANSWER: it is not clear what would be the head of the empty list `[]`.

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A

head : {A : Set} → List A → Maybe A
head [] = nothing        -- as found by C-c C-a
head (x :: xs) = just x  -- C-c C-a finds `head xs`.

tail : {A : Set} → List A → Maybe (List A)
tail [] = nothing        -- as found by C-c C-a
tail (x :: xs) = just xs -- C-c C-a finds `tail xs`

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

++-test₁ : example-list ++ [] ≡ example-list
++-test₁ = refl

++-test₂ : (1 :: []) ++ (2 :: 3 :: []) ≡ example-list
++-test₂ = refl

++-length : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
++-length [] ys = refl
++-length (x :: xs) ys = cong suc (++-length xs ys)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

map-test : map suc example-list ≡ 2 :: 3 :: 4 :: []
map-test = refl

double-all : List Nat → List Nat
double-all xs = map (λ x → x + x) xs

double-all-test : double-all example-list ≡ 2 :: 4 :: 6 :: []
double-all-test = refl

map-length : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
map-length f [] = refl
map-length f (x :: xs) = cong suc (map-length f xs)

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] n = nothing
lookup (x :: xs) zero = just x
lookup (x :: xs) (suc n) = lookup xs n

lookup-test₁ : lookup example-list 1 ≡ just 2
lookup-test₁ = refl

lookup-test₂ : lookup example-list 5 ≡ nothing
lookup-test₂ = refl



-- Part 2: Vectors
--================

data Vec (A : Set) : Nat → Set where
  []v : Vec A 0
  _::v_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 15 _::v_

example-vec : Vec Nat 3
example-vec = 1 ::v 2 ::v 3 ::v []v

head-v : {A : Set} {n : Nat} → Vec A (suc n) → A
head-v {A} {n} (x ::v xs) = x

tail-v : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail-v {A} {n} (x ::v xs) = xs

-- Create a vector of length n containing only the number 0:
zero-vec : (n : Nat) → Vec Nat n
zero-vec zero = []v
zero-vec (suc n) = 0 ::v (zero-vec n)

_++v_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[]v ++v ys = ys
(x ::v xs) ++v ys = x ::v (xs ++v ys)

map-v : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
map-v {A} {B} {.0} f []v = []v
map-v {A} {B} {.(suc _)} f (x ::v xs) = (f x) ::v (map-v f xs)

_·_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
[]v · []v = zero
(x ::v xs) · (y ::v ys) = (x * y) + (xs · ys)

·-test : example-vec · map-v suc example-vec ≡ 20
·-test = refl

data Fin : Nat → Set where
  zero-f : {n : Nat} → Fin (suc n)
  suc-f  : {n : Nat} → Fin n → Fin (suc n)
  
zero-Fin3 : Fin 3
zero-Fin3 = zero-f

one-Fin3 : Fin 3
one-Fin3 = suc-f zero-f

two-Fin3 : Fin 3
two-Fin3 = suc-f (suc-f zero-f)

lookup-v : {A : Set} {n : Nat} → Fin n → Vec A n → A
lookup-v {A} {.(suc _)} zero-f (x ::v xs) = x
lookup-v {A} {.(suc _)} (suc-f i) (x ::v xs) = lookup-v i xs

put-v : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
put-v zero-f a (x ::v xs) = a ::v xs
put-v (suc-f i) a (x ::v xs) = x ::v put-v i a xs

put-v-test : put-v one-Fin3 7 example-vec ≡ 1 ::v 7 ::v 3 ::v []v
put-v-test = refl




-- Part 3: The Sigma type
--=======================

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

IsEven : Nat → Set
IsEven n = Σ[ m ∈ Nat ] (2 * m ≡ n)
4-is-even : IsEven 4
4-is-even = 2 , refl

_×_ : Set → Set → Set
A × B = Σ[ _ ∈ A ] B

proj₁ : {A : Set} {B : A → Set} → (p : Σ[ x ∈ A ] (B x)) → A
proj₁ (x , y) = x

proj₂ : {A : Set} {B : A → Set} → (p : Σ[ x ∈ A ] (B x)) → B (proj₁ p)
proj₂ (x , y) = y

NonZero : Set
NonZero = Σ[ n ∈ Nat ] (is-zero n ≡ false)

pred : NonZero → Nat
pred (zero , ())
pred (suc n , eq) = n



-- Part 4: The Pi type
--=======================
Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x
syntax Π A (λ x → B-of-x) = Π[ x ∈ A ] B-of-x

n-n≡0 : (n : Nat) → (n - n) ≡ 0
n-n≡0 zero = refl
n-n≡0 (suc n) = n-n≡0 n



-- Part 5: A verified sorting algorithm
--=====================================

data _≤_ : Nat → Nat → Set where
  lz : {n : Nat} → zero ≤ n
  ls : {m n : Nat} → m ≤ n → suc m ≤ suc n
infix 2 _≤_

refl≤ : {n : Nat} → n ≤ n
refl≤ {zero} = lz
refl≤ {suc n} = ls refl≤

trans≤ : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
trans≤ {.0} {m} {n} lz m≤n = lz
trans≤ {.(suc _)} {.(suc _)} {.(suc _)} (ls l≤m) (ls m≤n) = ls (trans≤ l≤m m≤n)

_≤all_ : Nat → List Nat → Set
n ≤all [] = ⊤
n ≤all (x :: xs) = (n ≤ x) × (n ≤all xs)

trans-≤all : {m n : Nat} → {xs : List Nat} → (m ≤ n) → (n ≤all xs) → (m ≤all xs)
trans-≤all {m} {n} {[]} m≤n n≤[] = tt
trans-≤all {m} {n} {x :: xs} m≤n (n≤x , n≤xs) = trans≤ m≤n n≤x , (trans-≤all m≤n n≤xs)

IsSorted : List Nat → Set
IsSorted [] = ⊤
IsSorted (x :: xs) = (x ≤all xs) × IsSorted xs

SortedList : Set
SortedList = Σ[ xs ∈ List Nat ] (IsSorted xs)

compare : (m n : Nat) → (m ≤ n) ⊎ (n ≤ m)
compare zero n = left lz
compare (suc m) zero = right lz
compare (suc m) (suc n) with compare m n
compare (suc m) (suc n) | left m≤n = left (ls m≤n)
compare (suc m) (suc n) | right n≤m = right (ls n≤m)

{-# TERMINATING #-}
insert : (n : Nat) → (xs : SortedList) → List Nat
insert n ([] , []-sorted) = n :: []
insert n ((x :: xs) , x::xs-sorted) with compare n x
insert n ((x :: xs) , (x≤xs , xs-sorted)) | left n≤x = n :: x :: xs
insert n ((x :: xs) , (x≤xs , xs-sorted)) | right x≥n = x :: insert n (xs , xs-sorted)
{-
-- Note: some versions of Agda may issue a termination error for the above implementation of `insert`.
-- We know that `insert` terminates because the second argument of the recursive call has a smaller first component,
-- i.e. `xs` instead of `x :: xs`. You may need to help Agda by splitting up (currying) the pair in an auxiliary function,
-- as below:
insert' : (n : Nat) → (xs : List Nat) → IsSorted xs → List Nat
insert' n [] []-sorted = n :: []
insert' n (x :: xs) x::xs-sorted with compare n x
insert' n (x :: xs) x::xs-sorted | left n≤x = n :: x :: xs
insert' n (x :: xs) (x≤xs , xs-sorted) | right x≤n = x :: insert' n xs xs-sorted

insert : (n : Nat) → (xs : SortedList) → List Nat
insert n (xs , xs-sorted) = insert' n xs xs-sorted
-}

insert-≤all : {m : Nat} → (n : Nat) → m ≤ n → (xs : SortedList) → m ≤all proj₁ xs → m ≤all insert n xs
insert-≤all {m} n m≤n ([] , []-sorted) m≤[] = m≤n , tt
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) m≤x::xs with compare n x
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) m≤x::xs | left n≤x = m≤n , m≤x::xs
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) (m≤x , m≤xs) | right x≤n =
  m≤x , insert-≤all n (trans≤ m≤x x≤n) (xs , xs-sorted) m≤xs

{-# TERMINATING #-}
insert-is-sorted : (n : Nat) → (xs : SortedList) → IsSorted (insert n xs)
insert-is-sorted n ([] , []-sorted) = tt , tt
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) with compare n x
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) | left n≤x = (n≤x , (trans-≤all n≤x x≤xs)) , (x≤xs , xs-sorted)
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n =
  insert-≤all n x≤n (xs , xs-sorted) x≤xs , insert-is-sorted n (xs , xs-sorted)
{-
-- Same remark as for insert.
insert-is-sorted' : (n : Nat) → (xs : List Nat) → (xs-sorted : IsSorted xs) → IsSorted (insert n (xs , xs-sorted))
insert-is-sorted' n [] []-sorted = tt , tt
insert-is-sorted' n (x :: xs) (x≤xs , xs-sorted) with compare n x
insert-is-sorted' n (x :: xs) (x≤xs , xs-sorted) | left n≤x = (n≤x , (trans-≤all n≤x x≤xs)) , (x≤xs , xs-sorted)
insert-is-sorted' n (x :: xs) (x≤xs , xs-sorted) | right x≤n =
  insert-≤all n x≤n (xs , xs-sorted) x≤xs , insert-is-sorted' n xs xs-sorted

insert-is-sorted : (n : Nat) → (xs : SortedList) → IsSorted (insert n xs)
insert-is-sorted n (xs , xs-sorted) = insert-is-sorted' n xs xs-sorted
-}

insert-sorted : Nat → SortedList → SortedList
insert-sorted n xs = insert n xs , insert-is-sorted n xs

sort : List Nat → SortedList
sort [] = [] , tt
sort (x :: xs) = insert-sorted x (sort xs)

test-list : List Nat
test-list = 3 :: 1 :: 2 :: 76 :: 34 :: 15 :: 155 :: 11 :: 1 :: []

test-sort : proj₁ (sort test-list) ≡ 1 :: 1 :: 2 :: 3 :: 11 :: 15 :: 34 :: 76 :: 155 :: []
test-sort = refl





example : {x y : Nat} → x + y ≡ x * x → IsEven (x + y) → IsEven (x * x)
example {x} {y} p x+y-is-even with x + y
example {x} {y} refl x+y-is-even | .(x * x) = x+y-is-even
