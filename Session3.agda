
{-

|---------------------------------------------------|
| Formal systems and their applications: exercises  |
| Session 3: Formalization of programming languages |
|---------------------------------------------------|

In this exercise session, the goal will be to see how Agda can be used to formalize
syntax, evaluation rules, and typing rules of programming languages. In this session,
you will do this for a very simple calculus, typed arithmetic expressions from
chapter 8 of "Types and Programming Languages". In the project for this course, you
will have to do the same for a more complicated language.
So you can see this exercise session as a kind of warm-up for the project.

-}

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)


-- Part 1: Untyped boolean terms
--==============================
-- First, we will define the basic syntax of a very simple untyped language of boolean
-- expressions (see TAPL p. 34):
data Term : Set where
  tmTrue   : Term
  tmFalse  : Term
  tmIf     : (t1 t2 t3 : Term) → Term

-- As a Warm-up exercise, define a function to calculate the size of a term
-- (see TAPL p. 29):
size : Term → Nat
size t = {!!}

-- In contrast to the TAPL book, in Agda we usually don't define a separate syntactic
-- class of values. Instead, we define a predicate "IsValue t" on terms that expresses
-- that the term t is a value.
data IsValue : Term → Set where
  valTrue  : IsValue tmTrue
  valFalse : IsValue tmFalse

-- To give the operational semantics of our language, we define the one-step evaluation
-- relation ↝ (unicode input: \r~) as an indexed datatype in Agda.
data _↝_ : Term → Term → Set where
  e-IfTrue : {t2 t3 : Term} → ((tmIf tmTrue t2 t3) ↝ t2)
  -- Add more constructors here, one for each evaluation rule

-- A term is normal if it doesn't evaluate any further
IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥

-- Prove that all values are normal (Theorem 3.5.7 of TAPL):
values-normal : {t : Term} → IsValue t → IsNormal t
values-normal {t} vt {t'} et = {!!}


-- _↝*_ is the multi-step evaluation relation:
-- x ↝* y means that x ↝ x1 ↝ x2 ↝ ... ↝ y
data _↝*_ : Term → Term → Set where
  done : {x : Term} → (x ↝* x)
  step_,_ : {x x1 y : Term} → (x ↝ x1) → (x1 ↝* y) → (x ↝* y)
infixr 0 step_,_

-- Exercise: as a test, state and prove that
--   if t then false else false ↝* false
-- where
--   s = if true then false else false
--   t = if s then true else true
-- Note: proving should be possible using C-c C-a.

test-eval1 : {!!} ↝* {!!}
test-eval1 = {!!}


-- Part 2: Untyped arithmetic terms
--=================================

-- As an exercise, add new syntactic forms and evaluation rules for natural numbers
-- to the definitions above (see TAPL p. 41). Also add extra cases to the other 
-- functions so that everything typechecks again. You will need to define a new
-- datatype IsNumValue : Term → Set that describes when a term is a numeric value.
--   (When making changes, it is best to comment out all that follows, to make Agda
--   stop complaining. That way, you can make your document consistent again
--   definition by definition.)

-- Exercise: as a test, state and prove that
--   if false then 0 else (pred (suc (pred 0))) ↝* 0

test-eval2 : {!!} ↝* {!!}
test-eval2 = {!!}



-- Part 3: Typed arithmetic terms
--===============================

-- Now we will define a type system for this simple language of booleans and
-- natural numbers. It has two types: Bool and Nat.
data Type : Set where
  tyBool : Type
  tyNat  : Type

-- As with the evaluation rules, we encode the typing rules as a data type
-- We use the unicode symbol ∈ (input \in) instead of a colon because the colon
-- is already reserved by Agda.
-- We use the prefix d- for elements of this type, which are called [d]erivations.
data _∈_ : Term → Type → Set where
  d-True : tmTrue ∈ tyBool
  -- insert more constructors here (one for each typing rule on TAPL p. 93)

-- As a test, prove that the term `if (iszero 0) then 0 else (pred 0)`
-- has type Nat.
test-typing : {!!} ∈ tyNat
test-typing = {!!}

-- Inversion lemmas (see TAPL p. 94):
inversion-true : {tyR : Type} → tmTrue ∈ tyR → tyR ≡ tyBool
inversion-true {tyR} d = {!!}

-- Exercise: state and prove at least two more inversion lemmas


-- Uniqueness of types (see TAPL p. 94):
uniqueness-of-types : {t : Term} {tyT1 tyT2 : Type} → t ∈ tyT1 → t ∈ tyT2 → tyT1 ≡ tyT2
uniqueness-of-types d1 d2 = {!!}

-- Part 4: Safety = progress + preservation (see TAPL p. 96-97)
--=============================================================

-- First, prove the canonical forms lemma (lemma 8.3.1):
canonical-forms-bool : {t : Term} → (IsValue t) → (t ∈ tyBool) → (t ≡ tmTrue) ⊎ (t ≡ tmFalse)
canonical-forms-bool vt dt = {!!}

-- Also state and prove the canonical forms lemma for the Nat type:
-- (i.e. prove that any value of type Nat is a numeric value)
canonical-forms-nat : {!!}
canonical-forms-nat = {!!}

-- Now you are ready to prove progress and preservation of this language.


preservation : {t t' : Term} {tyT : Type} → (t ↝ t') → (t ∈ tyT) → (t' ∈ tyT)
preservation e1 d1 = {!!}

-- Hint: you can use the `with` syntax to pattern match on the value of a
-- function call. For an example of how to use `with`, you can look at
-- the solution of the first exercise session.

-- Hint: you can write _ as an expression; Agda will then infer its value.
-- This is only possible when only one value would type-check (e.g. the first
-- component of a dependent pair).

progress : {t : Term} {tyT : Type} → t ∈ tyT → (IsValue t) ⊎ (Σ[ t' ∈ Term ] (t ↝ t'))
progress d1 = {!!}

-------------------------------------------------------
-- Challenge: Prove normalization of this calculus.

-- The following lemmas are straightforward
-- to prove in terms of their counterparts that operate on ↝ instead of ↝*,
-- and may come in handy.

preservation* : {t t' : Term} {tyT : Type} → (t ↝* t') → (t ∈ tyT) → (t' ∈ tyT)
preservation* t↝*t' dt = {!!}

map* : {f : Term → Term}
  → (f↝ : {t t' : Term} → t ↝ t' → f t ↝ f t')
  → {t t' : Term} → t ↝* t' → f t ↝* f t'
map* f↝ et* = {!!}

step*_,_ : ∀ {t t' t''} → t ↝* t' → t' ↝* t'' → t ↝* t''
step* et* , et*' = {!!}

--now prove normalization

normalization : ∀ {t tyT} → t ∈ tyT → Σ[ t' ∈ Term ] ((t ↝* t') × IsValue t')
normalization dt = {!!}
