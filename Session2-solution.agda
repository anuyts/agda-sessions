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

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
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
  _::_ : (x : A) (xs : List A) → List A

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
  [] : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

example-vec : Vec Nat 3
example-vec = 1 :: 2 :: 3 :: []

head-Vec : {A : Set} {n : Nat} → Vec A (suc n) → A
head-Vec {A} {n} (x :: xs) = x

tail-Vec : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail-Vec {A} {n} (x :: xs) = xs

-- Create a vector of length n containing only the number 0:
zero-vec : (n : Nat) → Vec Nat n
zero-vec zero = []
zero-vec (suc n) = 0 :: (zero-vec n)

_++Vec_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

map-Vec : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
map-Vec {A} {B} {.0} f [] = []
map-Vec {A} {B} {.(suc _)} f (x :: xs) = (f x) :: (map-Vec f xs)

_·_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
[] · [] = zero
(x :: xs) · (y :: ys) = (x * y) + (xs · ys)

·-test : example-vec · map-Vec suc example-vec ≡ 20
·-test = refl

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)
  
zero-Fin3 : Fin 3
zero-Fin3 = zero

one-Fin3 : Fin 3
one-Fin3 = suc zero

two-Fin3 : Fin 3
two-Fin3 = suc (suc zero)

lookup-Vec : {A : Set} {n : Nat} → Fin n → Vec A n → A
lookup-Vec {A} {.(suc _)} zero (x :: xs) = x
lookup-Vec {A} {.(suc _)} (suc i) (x :: xs) = lookup-Vec i xs

put-Vec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
put-Vec zero a (x :: xs) = a :: xs
put-Vec (suc i) a (x :: xs) = x :: put-Vec i a xs

put-Vec-test : put-Vec one-Fin3 7 example-vec ≡ 1 :: 7 :: 3 :: []
put-Vec-test = refl




-- Part 3: The Sigma type
--=======================

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) (y : B x) → Σ A B

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
pred (suc x , y) = x



-- Part 4: A verified sorting algorithm
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
compare (suc m) (suc n) | left x = left (ls x)
compare (suc m) (suc n) | right x = right (ls x)

insert : (n : Nat) → (xs : SortedList) → List Nat
insert n ([] , []-sorted) = n :: []
insert n ((x :: xs) , x::xs-sorted) with compare n x
insert n ((x :: xs) , (x≤xs , xs-sorted)) | left n≤x = n :: x :: xs
insert n ((x :: xs) , (x≤xs , xs-sorted)) | right x≥n = x :: insert n (xs , xs-sorted)

insert-≤all : {m : Nat} → (n : Nat) → m ≤ n → (xs : SortedList) → m ≤all proj₁ xs → m ≤all insert n xs
insert-≤all {m} n m≤n ([] , []-sorted) m≤[] = m≤n , tt
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) m≤x::xs with compare n x
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) m≤x::xs | left n≤x = m≤n , m≤x::xs
insert-≤all {m} n m≤n ((x :: xs) , (x≤xs , xs-sorted)) (m≤x , m≤xs) | right x≤n =
  m≤x , insert-≤all n (trans≤ m≤x x≤n) (xs , xs-sorted) m≤xs

insert-is-sorted : (n : Nat) → (xs : SortedList) → IsSorted (insert n xs)
insert-is-sorted n ([] , []-sorted) = tt , tt
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) with compare n x
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) | left n≤x = (n≤x , (trans-≤all n≤x x≤xs)) , (x≤xs , xs-sorted)
insert-is-sorted n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n =
  insert-≤all n x≤n (xs , xs-sorted) x≤xs , insert-is-sorted n (xs , xs-sorted)

insert-sorted : Nat → SortedList → SortedList
insert-sorted n xs = insert n xs , insert-is-sorted n xs

sort : List Nat → SortedList
sort [] = [] , tt
sort (x :: xs) = insert-sorted x (sort xs)

test-list : List Nat
test-list = 3 :: 1 :: 2 :: 76 :: 34 :: 15 :: 155 :: 11 :: 1 :: []

test-sort : proj₁ (sort test-list) ≡ 1 :: 1 :: 2 :: 3 :: 11 :: 15 :: 34 :: 76 :: 155 :: []
test-sort = refl





ifDec_then_else_ : {A B : Set} → Dec A → B → B → B
ifDec yes x then b₁ else b₂ = b₁
ifDec no x then b₁ else b₂ = b₂

case_return_of_ : ∀ {A : Set} → (a : A) → (B : A → Set) → ((x : A) → B x) → B a
case a return B of f = f a

if-ifnot : ∀ {A : Set} {b : Bool} {x y : A} → (if b then x else y) ≡ (if ¬ b then y else x)
if-ifnot {A}{b}{x}{y} =
  case b
  return (λ b' → (if b' then x else y) ≡ (if ¬ b' then y else x))
  of λ { false → refl ; true → refl }

count : Nat → List Nat → Nat
count n [] = 0
count n (x :: xs) = ifDec equalNat? n x then suc (count n xs) else count n xs

{- or directly:
count : Nat → List Nat → Nat
count n [] = zero
count n (x :: xs) with equalNat? n x
count n (x :: xs) | yes _ = suc (count n xs)
count n (x :: xs) | no _ = count n xs
-}

HaveSameContents : List Nat → List Nat → Set
HaveSameContents xs ys = (n : Nat) → count n xs ≡ count n ys

count-insert : (m n : Nat) → (xs : SortedList) →
  count m (insert n xs) ≡ (ifDec equalNat? m n then suc else λ k → k) (count m (proj₁ xs))
count-insert m n ([] , []-sorted) with equalNat? m n
count-insert m n ([] , []-sorted) | yes x = refl
count-insert m n ([] , []-sorted) | no x = refl
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) with compare n x
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | left n≤x with equalNat? m n
count-insert m n ((x₁ :: xs) , (x≤xs , xs-sorted)) | left n≤x | (yes _) = refl
count-insert m n ((x₁ :: xs) , (x≤xs , xs-sorted)) | left n≤x | (no _) = refl
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n
  with equalNat? m n | equalNat? m x | count-insert m n (xs , xs-sorted)
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n | (yes x₁) | (yes x₂) | e = cong suc e
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n | (no x₁) | (yes x₂) | e = cong suc e
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n | (yes x₁) | (no x₂) | e = e
count-insert m n ((x :: xs) , (x≤xs , xs-sorted)) | right x≤n | (no x₁) | (no x₂) | e = e

sort-permutes : (xs : List Nat) → HaveSameContents xs (proj₁ (sort xs))
sort-permutes [] n = refl
sort-permutes (x :: xs) n with equalNat? n x | count-insert n x (sort xs)
sort-permutes (x :: xs) n | yes _ | e = trans (cong suc (sort-permutes xs n)) (sym e)
sort-permutes (x :: xs) n | no _ | e = trans (sort-permutes xs n) (sym e)
