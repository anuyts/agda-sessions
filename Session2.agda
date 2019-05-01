{-

|--------------------------------------------------|
| Formal systems and their applications: exercises |
| Session 2: Lists and vectors                     |
|--------------------------------------------------|

-}



-- Part 0: A note on the Agda standard library
--============================================

{-
-- You can either import the solution of the previous exercise session:
open import Session1
-}

{- Or you can import the necessary materials from the Agda standard library (is-zero needs to be reimplemented).

   An import with a `renaming` clause renames objects as mentioned.
   An import with a `hiding` clause hides the mentioned objects.
   An import with a `using` clause hides all objects that are not mentioned.

   In emacs, you can jump to a file or to the definition of an object, by clicking it with the middle mouse button.

   Some files contain public imports. E.g. Data.Nat contains a public import of Data.Nat.Base,
   so that if you import Data.Nat, then all contents of Data.Nat.Base will also be available.

   For the project, we will use the Agda standard library.
-}
--Natural numbers and related tools.
open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
--Propositional equality
--  Write `open ≡-Reasoning` to get access to some tools for proving equality.
open import Relation.Binary.PropositionalEquality
--Booleans.
open import Data.Bool renaming (not to ¬)
--The unit type (⊤).
open import Data.Unit hiding (_≤_)
--The disjoint union type _⊎_ .
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)
--Among other things: decidability (Dec).
open import Relation.Nullary hiding (¬_)
is-zero : Nat → Bool
is-zero zero = true
is-zero (suc n) = false


-- Part 1: Lists
--==============

-- As in Haskell, we can give an inductive definition of lists in Agda:
--   []       is the empty list
--   x :: xs  is a list with head x and tail xs
data List (A : Set) : Set where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A
-- (The advantage of naming the constructor's arguments, is that Agda will use these names
-- as default names when pattern matching using C-c C-c.)

-- Note that an arrow is missing in the type of _::_. See agda.readthedocs.io > function types
-- for details on how function types may be abbreviated.

-- The infix statement allows us to write fewer parentheses
infixr 15 _::_

example-list : List Nat
example-list = 1 :: 2 :: 3 :: []

-- Write a function that calculates the length of a given list:
length : {A : Set} → List A → Nat
length xs = {!!}

-- Here are some tests for the 'length' function. If your implementation is correct,
-- you should be able to fill in 'refl':
length-test₁ : length {A = Nat} [] ≡ 0
length-test₁ = {!!}

length-test₂ : length example-list ≡ 3
length-test₂ = {!!}

-- Basic operations on lists include taking the head and the tail of the list.
-- First, try to explain why we cannot define a head function of type
-- `{A : Set} → List A →  A`.

-- An element of `Maybe A` is either `just x` or `nothing`
-- `nothing` is often used to signal some kind of error.
data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A

-- Get the head and tail of a list, returning nothing if the list is empty
--     Good to know: pressing C-c C-a when in a hole, makes Agda look for SOME term
--     of the correct type. Try it here to get an idea of how helpful/dangerous it is.
--     You are always allowed to use this feature, and always recommended to be skeptical
--     about its output.
head : {A : Set} → List A → Maybe A
head xs = {!!}

tail : {A : Set} → List A → Maybe (List A)
tail xs = {!!}

-- Write a function to append two lists together:
_++_ : {A : Set} → List A → List A → List A
xs ++ ys = {!!}

++-test₁ : example-list ++ [] ≡ example-list
++-test₁ = {!!}

++-test₂ : (1 :: []) ++ (2 :: 3 :: []) ≡ example-list
++-test₂ = {!!}

-- Prove that the length of the concatenation of two lists is the sum of the
-- lengths of the two lists:
++-length : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
++-length xs ys = {!!}

-- map should apply a function to every element in a list
map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}

map-test : map suc example-list ≡ 2 :: 3 :: 4 :: []
map-test = {!!}

double-all : List Nat → List Nat
double-all xs = map (λ x → x + x) xs
-- lambda expressions can be used to define in-line functions

double-all-test : double-all example-list ≡ 2 :: 4 :: 6 :: []
double-all-test = {!!}

-- prove that mapping a function over a list preserves its length
map-length : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
map-length f xs = {!!}


-- Next, let's implement a lookup operator: given a list and a number n,
-- select the n'th element from this list.
lookup : {A : Set} → List A → Nat → Maybe A
lookup xs n = {!!}

lookup-test₁ : lookup example-list 1 ≡ just 2
lookup-test₁ = {!!}

lookup-test₂ : lookup example-list 5 ≡ nothing
lookup-test₂ = {!!}



-- Part 2: Vectors
--================

-- In a dependently typed language like Agda, there is a different way to define lists
-- that gives better guarantees about the length of the list:

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

{-
The first line declares `Vec A` as a function mapping natural numbers to "sets" (types).
Namely, the number `n` will be mapped to the type `Vec A n` of vectors over `A` of
length `n`. There is a subtle distinction between *parameters* such as `A` (declared
before the colon) and *indices* such as `n` (declared after it):
the constructors can determine the indices,
but not the parameters of their output. Try replacing the first line with
`data Vec (A : Set) (n : Nat) : Set where` and observe the error.

The other lines declare the constructors. Note how they interact with the index n.
-}

example-vec : Vec Nat 3
example-vec = 1 :: 2 :: 3 :: []
-- example-vec = 1 :: 2 :: []
-- ^ this example wouldn't typecheck, as the length is 2, but the type is 'Vec Nat 3'

-- If we use vectors, we don't need Maybe in the return type of head and tail.
-- Instead, we only allow these functions to be called on a vector of length at
-- least one (i.e. a vector of type 'Vec A (suc n)' for some n : Nat).
head-Vec : {A : Set} {n : Nat} → Vec A (suc n) → A
head-Vec {A} {n} xs = {!!}

tail-Vec : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail-Vec {A} {n} xs = {!!}

-- Create a vector of length n containing only the number 0:
zero-vec : (n : Nat) → Vec Nat n
zero-vec n = {!!}

-- Other functions on lists, such as _++_ and map, can also be written for vectors but
-- now the types describe their effect on the length of the vector.
-- Thanks to the more informative types, C-c C-r (refine) will be more helpful in empty
-- goals, and C-c C-a (program/proof search) will get it right more often.

-- Remark that in Agda, we can overload constructor names but not function names.
_++Vec_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
xs ++Vec ys = {!!}

map-Vec : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
map-Vec {A}{B}{n} f xs = {!!}

-- It is also possible to enforce that two input vectors have the same length.
-- For example, we can calculate the dot product (as in physics) of two vectors (unicode \cdot):
_·_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
xs · ys = {!!}

·-test : example-vec · map-Vec suc example-vec ≡ 20
·-test = {!!}

-- In order to implement a lookup function on vectors, we first need to
-- introduce the Fin type: this is the type of natural numbers up to a given
-- boundary, i.e. Fin n contains the numbers 0,1,2,...,n-1
-- These types are called Fin n because all finite types with n elements are
-- isomorphic to Fin n.
data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

-- Fin 3 contains the elements `zero`, `suc zero`, and `suc (suc zero)`:
zero-Fin3 : Fin 3
zero-Fin3 = zero

one-Fin3 : Fin 3
one-Fin3 = suc zero

two-Fin3 : Fin 3
two-Fin3 = suc (suc zero)

-- ... but not `suc (suc (suc zero))`:
--three-Fin3 : Fin 3
--three-Fin3 = suc (suc (suc zero))

-- (try to uncomment the above definition to see what goes wrong).

-- Now that we have the Fin type, we can write a version of lookup on vectors
-- that doesn't have Maybe in its return type. Try to do this now:
lookup-Vec : {A : Set} {n : Nat} → Fin n → Vec A n → A
lookup-Vec {A}{n} i xs = {!!}

-- Notice that the type of this function guarantees that the index i will never
-- be out of the bounds of the vector xs.

-- Also write a function that sets the i-th value in a vector to a given value:
put-Vec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
put-Vec i a xs = {!!}

put-Vec-test : put-Vec one-Fin3 7 example-vec ≡ 1 :: 7 :: 3 :: []
put-Vec-test = {!!}




-- Part 3: The Sigma type
--=======================

-- Another very important type for dependently typed programming (and proving) is
-- the Σ-type (unicode input: \Sigma or \GS). You can think of it as a type of tuples
-- (x , y) where the type of y can depend on the value of x.
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) (y : B x) → Σ A B

-- This syntax declaration allows us to write Σ[ x ∈ A ] (B x) instead of Σ A (λ x → B x):
syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

{-
Under the Curry-Howard correspondence, `Σ[ x ∈ A ] (B x)` means "there is some `x : A`
such that B x is true". For example:
-}
IsEven : Nat → Set
IsEven n = Σ[ m ∈ Nat ] (2 * m ≡ n)
4-is-even : IsEven 4
4-is-even = {!!}

-- The Σ-type is also a generalization of the product type, which encodes the logical operator 'and':
_×_ : Set → Set → Set
A × B = Σ[ _ ∈ A ] B

-- The projection functions project out the components of a Σ type.
-- Note that the return type of proj₂ depends on the result of the
-- first projection proj₁.
proj₁ : {A : Set} {B : A → Set} → (p : Σ[ x ∈ A ] (B x)) → A
proj₁ (x , y) = x

proj₂ : {A : Set} {B : A → Set} → (p : Σ[ x ∈ A ] (B x)) → B (proj₁ p)
proj₂ (x , y) = y


-- Σ is often used to define subtypes. For example, using Σ and the function
-- is-zero, we can define a type of nonzero natural numbers:
NonZero : Set
NonZero = Σ[ n ∈ Nat ] (is-zero n ≡ false)

-- Now we can write a function that calculates the predecessor of a nonzero
-- natural number, without resorting to using a Maybe type:
pred : NonZero → Nat
pred n = {!!}




-- Part 4: A verified sorting algorithm
--=====================================
-- As a bigger example, we will define a type of sorted lists of natural numbers.

-- First, we define inequality of natural numbers (input \le or \≤ or on some keyboards alt+<):
data _≤_ : Nat → Nat → Set where
  lz : {n : Nat} → zero ≤ n
  ls : {m n : Nat} → m ≤ n → suc m ≤ suc n
infix 2 _≤_

-- Show that inequality is reflexive and transitive:
refl≤ : {n : Nat} → n ≤ n
refl≤ {n} = {!!}

trans≤ : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
trans≤ {l}{m}{n} l≤m m≤n = {!!}

-- Now define what it means that n is less than or equal to
-- all elements of the list xs.
-- Use the Curry-Howard correspondence (see previous session) to
-- encode propositions as types.
_≤all_ : Nat → List Nat → Set
n ≤all xs = {!!}

-- Prove mixed transitivity:
trans-≤all : {m n : Nat} → {xs : List Nat} → (m ≤ n) → (n ≤all xs) → (m ≤all xs)
trans-≤all {m}{n}{xs} m≤n n≤xs = {!!}

-- We use ≤all to define what it means for a list to be sorted:
IsSorted : List Nat → Set
IsSorted [] = ⊤
IsSorted (x :: xs) = (x ≤all xs) × IsSorted xs
{- This is a bit overkill: in the list `x :: y :: z :: []`,
   we are requiring that x ≤ y, x ≤ z and y ≤ z. Of course, x ≤ z follows from the
   other inequalities by transitivity. However, reasoning about sortedness becomes a
   LOT easier if we include these superfluous inequalities.
-}

-- In analogy to the NonZero type, we define a type of sorted lists:
SortedList : Set
SortedList = Σ[ xs ∈ List Nat ] (IsSorted xs)

-- We need to be able to decide which of two numbers is greater.
-- This could be done by implementing a term of type (m n : Nat) → Dec (m ≤ n),
-- but the following will be more practical:
--    Hint: you will likely need a with-clause.
compare : (m n : Nat) → (m ≤ n) ⊎ (n ≤ m)
compare m n = {!!}

-- Define a function that inserts a number into a sorted list.
--    Hint: you will likely need a with-clause.
insert : (n : Nat) → (xs : SortedList) → List Nat
insert n xs = {!!}

-- Show that if `m ≤ n` and `m` ≤ all elements of `xs`, then `m` ≤ all elements of
-- `insert n xs`.
insert-≤all : {m : Nat} → (n : Nat) → m ≤ n
  → (xs : SortedList) → m ≤all proj₁ xs → m ≤all insert n xs
insert-≤all {m} n m≤n (xs , xs-sorted) m≤xs = {!!}
{- Note: The proposition that you need to prove, contains a call to `insert`.
   It is then often a good idea to start with the same pattern matches and with-abstractions
   that you used in the definition of `insert`, so that the call properly reduces
   in each of the cases.
   When displaying the type, Agda will even append the content of the with-clause
   of `insert`, i.e.
      `m ≤all (insert n ((x :: xs) , (x≤xs , xs-sorted)))`
   will become
      `m ≤all (insert n ((x :: xs) , (x≤xs , xs-sorted)) | compare n x)`
   or similar (depending on your exact definition of `insert`).
-}

-- Show that `insert` preserves sortedness:
insert-is-sorted : (n : Nat) → (xs : SortedList) → IsSorted (insert n xs)
insert-is-sorted n (xs , xs-sorted) = {!!}

-- Pairing them up:
insert-sorted : Nat → SortedList → SortedList
insert-sorted n xs = insert n xs , insert-is-sorted n xs

-- Implement a `sort` function:
sort : List Nat → SortedList
sort xs = {!!}

test-list : List Nat
test-list = 3 :: 1 :: 2 :: 76 :: 34 :: 15 :: 155 :: 11 :: 1 :: []

-- If your implementation is correct, you should be able to fill in refl here:
test-sort : proj₁ (sort test-list) ≡ 1 :: 1 :: 2 :: 3 :: 11 :: 15 :: 34 :: 76 :: 155 :: []
test-sort = {!!}





{- Challenge:
The sort function produces sorted lists from lists. But so does the function 
(λ xs → ([], tt)) that maps
any list xs to the empty sorted list. What property uniquely defines sort? State it
and prove it.

The following tools might come in handy (although none of them is strictly necessary):
-}

ifDec_then_else_ : {A B : Set} → Dec A → B → B → B
ifDec cond then b₁ else b₂ = {!!}

-- The following is useful for inline pattern matching
case_return_of_ : ∀ {A : Set} → (a : A) → (B : A → Set) → ((x : A) → B x) → B a
case a return B of f = f a
-- For example:
if-ifnot : ∀ {A : Set} {b : Bool} {x y : A} → (if b then x else y) ≡ (if ¬ b then y else x)
if-ifnot {A}{b}{x}{y} =
  case b
  return (λ b' → (if b' then x else y) ≡ (if ¬ b' then y else x))
  of λ { false → refl ; true → refl }

-- `count n xs` counts the number of occurrences of `n` in `xs`:
count : Nat → List Nat → Nat
count n xs = {!!}
-- You can use `equalNat?` from last session.

{-
Two lists have the same contents if every number n occurs equally often in each one.
Under the Curry-Howard correspondence, "forall x : A, B x holds" translates to
`(x : A) → B x`
-}
HaveSameContents : List Nat → List Nat → Set
HaveSameContents xs ys = (n : Nat) → count n xs ≡ count n ys

{- Hint: You may need some advanced use of with-clauses.
When you add a with-clause for matching over some expression `expr`, then any
occurrence of `expr` in the goal type will be replaced by the pattern `p`.
However, this is only done in the goal type. If you want to make use of another
expression `thing` of type `B expr`, but you want to use it as having type `B p`,
then you have to add both in a single with-clause.
See: http://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html#simultaneous-abstraction
-}

