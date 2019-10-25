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
open import Session1 hiding (_×_)
-}

{- Xor you can import the necessary materials from the Agda standard library (is-zero needs to be reimplemented).

   An import with a `renaming` clause renames objects as mentioned.
   An import with a `hiding` clause hides the mentioned objects.
   An import with a `using` clause hides all objects that are not mentioned.

   In emacs, you can jump to a file or to the definition of an object, by clicking it with the middle mouse button.

   Some files contain public imports. E.g. Data.Nat contains a public import of Data.Nat.Base,
   so that if you import Data.Nat, then all contents of Data.Nat.Base will also be available.

   For the project, we will use the Agda standard library.
-}
--Natural numbers and related tools.
open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat? ; _∸_ to _-_) hiding (pred ; _≤_ ; compare)
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
  _::_ : (x : A) → (xs : List A) → List A
-- (The advantage of naming the constructor's arguments, is that Agda will use these names
-- as default names when pattern matching using C-c C-c.)

-- The infix statement determines the operator's priority and allows us to write fewer parentheses
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
-- lengths of the two lists.
-- Hint: This is easy if your definitions of _+_ and _++_ look very similar. If you're importing
-- session 1 rather than the standard library and are having difficulties,
-- then you may want to reconsider how you can define _+_ more similarly to _++_.
++-length : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
++-length xs ys = {!!}

-- map should apply a function to every element in a list
map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}

map-test : map suc example-list ≡ 2 :: 3 :: 4 :: []
map-test = {!!}

double-all : List Nat → List Nat
double-all xs = map (λ x → x + x) xs

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
  []v : Vec A 0
  _::v_ : {n : Nat} → A → Vec A n → Vec A (suc n)
  
infixr 15 _::v_

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
example-vec = 1 ::v 2 ::v 3 ::v []v
-- example-vec = 1 ::v 2 ::v []v
-- ^ this example wouldn't typecheck, as the length is 2, but the type is 'Vec Nat 3'

-- If we use vectors, we don't need Maybe in the return type of head and tail.
-- Instead, we only allow these functions to be called on a vector of length at
-- least one (i.e. a vector of type 'Vec A (suc n)' for some n : Nat).
head-v : {A : Set} {n : Nat} → Vec A (suc n) → A
head-v {A} {n} xs = {!!}

tail-v : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail-v {A} {n} xs = {!!}

-- Create a vector of length n containing only the number 0:
zero-vec : (n : Nat) → Vec Nat n
zero-vec n = {!!}

-- Other functions on lists, such as _++_ and map, can also be written for vectors but
-- now the types describe their effect on the length of the vector.
-- Thanks to the more informative types, C-c C-r (refine) will be more helpful in empty
-- goals, and C-c C-a (program/proof search) will get it right more often.

_++v_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
xs ++v ys = {!!}

map-v : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
map-v {A}{B}{n} f xs = {!!}

-- It is also possible to enforce that two input vectors have the same length.
-- For example, we can calculate the dot product (as in physics) of two vectors (unicode \cdot):
_·_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
xs · ys = {!!}

·-test : example-vec · map-v suc example-vec ≡ 20
·-test = {!!}

-- In order to implement a lookup function on vectors, we first need to
-- introduce the Fin type: this is the type of natural numbers up to a given
-- boundary, i.e. Fin n contains the numbers 0,1,2,...,n-1
-- These types are called Fin n because all finite types with n elements are
-- isomorphic to Fin n.
data Fin : Nat → Set where
  zero-f : {n : Nat} → Fin (suc n)
  suc-f  : {n : Nat} → Fin n → Fin (suc n)

-- Fin 3 contains the elements `zero`, `suc zero`, and `suc (suc zero)`:
zero-Fin3 : Fin 3
zero-Fin3 = zero-f

one-Fin3 : Fin 3
one-Fin3 = suc-f zero-f

two-Fin3 : Fin 3
two-Fin3 = suc-f (suc-f zero-f)

-- ... but not `suc-f (suc-f (suc-f zero-f))`:
-- three-Fin3 : Fin 3
-- three-Fin3 = suc-f (suc-f (suc-f zero-f))

-- (try to uncomment the above definition to see what goes wrong).

-- Now that we have the Fin type, we can write a version of lookup on vectors
-- that doesn't have Maybe in its return type. Try to do this now:
lookup-v : {A : Set} {n : Nat} → Fin n → Vec A n → A
lookup-v {A}{n} i xs = {!!}
-- Notice that the type of this function guarantees that the index i will never
-- be out of the bounds of the vector xs.

-- Also write a function that sets the i-th value in a vector to a given value:
put-v : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
put-v i a xs = {!!}

put-v-test : put-v one-Fin3 7 example-vec ≡ 1 ::v 7 ::v 3 ::v []v
put-v-test = {!!}




-- Part 3: The Sigma type
--=======================

-- Another very important type for dependently typed programming (and proving) is
-- the Σ-type (unicode input: \Sigma or \GS for Greek S), aka dependent pair type.
-- You can think of it as a type of pairs
-- (x , y) where the type of y can depend on the value of x.
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

-- This syntax declaration allows us to write Σ[ x ∈ A ] (B x) instead of Σ A (λ x → B x):
syntax Σ A (λ x → B-of-x) = Σ[ x ∈ A ] B-of-x

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



-- Part 4: The Pi type
--=======================
-- The Π-type or dependent function type is in theoretical papers and some other languages often
-- denoted with a Π, but not in Agda. Of course, we can define the symbol Π ourselves.
-- The Π-type is a type of functions `f` for which the type of `f x` depends on the value of `x`.
-- We've been using such dependent functions all along:
Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x
syntax Π A (λ x → B-of-x) = Π[ x ∈ A ] B-of-x
-- Of course, neither the symbol Π nor the syntax for it is very useful, as Agda provides primitive
-- syntax for dependent function types. So they are here just to demonstrate the parallel with the Σ-type.

{-
Under the Curry-Howard correspondence, `Π[ x ∈ A ] (B x)` or `(x : A) → B x` means
"for all `x : A`, `B x` is true." For example:
For all natural numbers n, n minus n equals 0:
-}
n-n≡0 : (n : Nat) → (n - n) ≡ 0
n-n≡0 n = {!!}



-- Part 5: A verified sorting algorithm
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




-- Part 6: Using equality proofs
--==============================
{-
A frequently asked question is: how can one use an equality proof.

The answer is: by pattern matching. Pattern matching over an equality proof p : a ≡ b is only possible if a and b

 * are obviously different (then you get an absurd pattern),
 * easy to equate.

If the equation is not easily solved, then you can turn one of its sides into a variable by with-abstracting over it.
Of course an equation in which one side is a variable, is easily solved.
You can find a good example in the Agda docs:
https://agda.readthedocs.io/en/v2.5.3/language/with-abstraction.html#simultaneous-abstraction

We will consider an example here as well. Suppose we know:
  x + y = x * x
Then clearly, if `x + y` is even, then so is `x + x`. Let's prove this:
-}
example : {x y : Nat} → x + y ≡ x * x → IsEven (x * x) → IsEven (x + y)
example {x} {y} p x*x-is-even = {!!}
{-
If you try to pattern-match on p, you get an error, because the equation is too difficult for Agda to solve.
For this reason, we first turn one side into a variable:
example {x} {y} p x*x-is-even with x * x
example {x} {y} p x*x-is-even | x*x = ?
Now, in the hole, the expression `x * x` is replaced with the variable `x*x` in the types of all variables in scope,
as well as in the required type of the hole.
If we subsequently pattern-match on p, then p becomes refl and --- as this is required for refl to be well-typed ---
the variable `x*x` is replaced with the expression `x + y`.
Thus, at this point, the type of `x*x-is-even` has become `IsEven (x + y)`, and the variable can simply be used on the right.
-}

{-
This technique is a bit subtle however. Suppose we know that the square of an even number is even:
-}
postulate
  even-square : {x : Nat} → IsEven x → IsEven (x * x)
{-
Let's try to prove the same, but from the knowledge that x is even.
-}
example2 : {x y : Nat} → x + y ≡ x * x → IsEven x → IsEven (x + y)
example2 {x} {y} p x-is-even with x * x
example2 {x} {y} p x-is-even | x*x = {!!}
{-
If we proceed as before:
  1. match over p
  2. fill out `even-square x-is-even` on the right
then we get an error: the type of `even-square x-is-even` has NOT become `IsEven (x + y)` but is still `IsEven (x * x)`.
The problem is that we came up with this expression AFTER with-abstracting over `x * x`.
The solution is to with-abstract over both simultaneously:
example2 {x} {y} p x-is-even with x * x | even-square x-is-even
example2 {x} {y} p x-is-even | x*x | x*x-is-even = {!!}
Now the type of `x*x-is-even` is `IsEven x*x` and pattern-matching over `p` will turn that into `IsEven (x + y)`.
-}
