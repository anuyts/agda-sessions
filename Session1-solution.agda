{-

|--------------------------------------------------|
| Formal systems and their applications: exercises |
| Session 1: Agda basics                           |
|--------------------------------------------------|

Part 1: Booleans and natural numbers
====================================

-}

data Bool : Set where
  true  : Bool
  false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ y = y
false ∧ y = false

_∨_ : Bool → Bool → Bool
true ∨ y = true
false ∨ y = y

if_then_else_ : {A : Set} → Bool → A → A → A
(if true  then x else y) = x
(if false then x else y) = y

¬-alt : Bool → Bool
¬-alt x = if x then false else true

weird : Bool → (Bool → Bool → Bool)
weird x = if x then _∧_ else _∨_

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

is-zero : Nat → Bool
is-zero zero = true
is-zero (suc n) = false

_-_ : Nat → Nat → Nat         -- Return zero instead of negative numbers
m - zero = m
zero - suc n = zero
suc m - suc n = m - n

minimum : Nat → Nat → Nat
minimum zero n = zero
minimum (suc m) zero = zero
minimum (suc m) (suc n) = suc (minimum m n)

maximum : Nat → Nat → Nat
maximum zero n = n
maximum (suc m) zero = suc m
maximum (suc m) (suc n) = suc (maximum m n)

_*_ : Nat → Nat → Nat
zero * n = zero
suc m * n = n + (m * n)

{-
Part 2: Proving basic properties
================================
-}

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where
  -- no constructors

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (a , b) = a

snd : {A B : Set} → A × B → B
snd (a , b) = b

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

×-comm : {A B : Set} → A × B → B × A
×-comm (a , b) = b , a

distr : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
distr (a , left b) = left (a , b)
distr (a , right c) = right (a , c)

app : {A B : Set} → (A → B) × A → B
app (f , a) = f a


{-
Part 3: Record types
====================
-}
record _×'_ (A B : Set) : Set where
  constructor _,'_
  field
    fst' : A
    snd' : B
open _×'_

×'-comm : {A B : Set} → A ×' B → B ×' A
fst' (×'-comm p) = snd' p
snd' (×'-comm p) = fst' p

×'-comm' : {A B : Set} → A ×' B → B ×' A
×'-comm' (x ,' y) = y ,' x

{-
Part 4: The identity type
=========================
-}

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

refl-example : 3 ≡ 3
refl-example = refl

--refl-counterexample : 3 ≡ 4
--refl-counterexample = {!cannot be done!}

refl-example' : 2 + 3 ≡ 5
refl-example' = refl

¬¬true : ¬ (¬ true) ≡ true
¬¬true = refl

3+5-5 : (3 + 5) - 5 ≡ 3
3+5-5 = refl

-- Write more tests here
test-min-max : minimum (maximum 1 2) (maximum 3 4) ≡ 2
test-min-max = refl
--

¬¬-elim : (b : Bool) → ¬ (¬ b) ≡ b
¬¬-elim true = refl
¬¬-elim false = refl

∧-same : (b : Bool) → b ∧ b ≡ b
∧-same true = refl
∧-same false = refl

if-same : {A : Set} → (b : Bool) → (x : A) → (if b then x else x) ≡ x
if-same true x = refl
if-same false x = refl


{-
Part 5: refl patterns and absurd patterns
=========================================
-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym {A}{x}{.x} refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A}{x}{.x}{.x} refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f {x} {.x} refl = refl

true-not-false : true ≡ false → ⊥
true-not-false ()

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

not-zero-and-one : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one zero eq0 ()
not-zero-and-one (suc n) () eq1

not-zero-and-one' : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one' .0 refl ()

not-zero-and-one'' : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one'' .1 () refl

∨-first : (b : Bool) → b ∨ false ≡ true → b ≡ true
∨-first true eq = refl
∨-first false ()

easy-match : {x : Nat} → suc x ≡ 3 → x ≡ 2
easy-match {.2} refl = refl

-- The main point here is that it's hard; depending on your definition of _*_ and _+_, it may be VERY hard.
-- Don't worry about not being able to complete this one, that just proves the point.
harder-match : {x : Nat} → x * 4 ≡ 12 → x ≡ 3
harder-match {zero} ()
harder-match {suc zero} ()
harder-match {suc (suc zero)} ()
harder-match {suc (suc (suc zero))} p = refl
harder-match {suc (suc (suc (suc x)))} ()
-- New versions of Agda may allow omission of all clauses but the `refl` one,
-- so that the solution is not that hard after all.

uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {A} {x} {.x} {refl} {refl} = refl



{-
Part 6: More properties of natural numbers
==========================================
-}
plus0-left : (n : Nat) → 0 + n ≡ n
plus0-left n = refl

plus0-right : (n : Nat) → n + 0 ≡ n
plus0-right zero = refl
plus0-right (suc n) = cong suc (plus0-right n)

plus0-right-example : 3 + 0 ≡ 3
plus0-right-example = plus0-right 3
--Can you figure out how Agda computes the following term? (Use C-c C-n to view the computation result.)
{- plus0-right 3
 = cong suc (plus0-right 2)
 = cong suc (cong suc (plus0-right 1))
 = cong suc (cong suc (cong suc (plus0-right 0)))
 = cong suc (cong suc (cong suc refl))
 = cong suc (cong suc refl)
 = cong suc refl
 = refl
-}

plus-assoc : (k l m : Nat) → k + (l + m) ≡ (k + l) + m
plus-assoc zero l m = refl
plus-assoc (suc k) l m = cong suc (plus-assoc k l m)

--auxiliary function
plus-suc-right : (m n : Nat) → suc (m + n) ≡ m + suc n
plus-suc-right zero n = refl
plus-suc-right (suc m) n = cong suc (plus-suc-right m n)

plus-comm : (m n : Nat) → m + n ≡ n + m
plus-comm zero n = sym (plus0-right n)
plus-comm (suc m) n = trans (cong suc (plus-comm m n)) (plus-suc-right n m)



{-
Part 7: Lambda-abstractions and functions
=========================================
-}
split-assumption : {A B C : Set} → (A ⊎ B → C) → (A → C) × (B → C)
split-assumption f = (λ a → f (left a)) , (λ b → f (right b))

split-assumption' : {A B C : Set} → (A ⊎ B → C) → (A → C) ×' (B → C)
fst' (split-assumption' f) a = f (left a)
snd' (split-assumption' f) b = f (right b)

{-
State and prove:
If A implies (B and C), then A implies B and A implies C
-}
split-conclusion : {A B C : Set} → (A → B × C) → (A → B) × (A → C)
split-conclusion f = (λ a → fst (f a)) , (λ a → snd (f a))

lemma : {A B : Set} → (A → B) → (A ⊎ ⊥ → B) × (⊥ → A)
lemma f = (λ where
               (left a) → f a
               (right ())
          ) , λ ()
lemma' : {A B : Set} → (A → B) → (A ⊎ ⊥ → B) × (⊥ → A)
lemma' f = (λ { (left a) → f a
              ; (right ())
              }
           ) , (λ ())

const : {A B : Set} → A → B → A
const a b = a
ambiguous-function : Bool → ⊥ → Nat
ambiguous-function bool bot =
  const {B = Bool} 5 (if bool then ⊥-elim bot else ⊥-elim bot)

if-zero : Nat → {A : Set} → A → A → A
if-zero = λ {zero    {A} a b → a ;
             (suc n) {A} a b → b}

refl₁ : {A : Set} → {a : A} → a ≡ a
refl₁ = refl

refl₂ : {A : Set} {a : A} → a ≡ a
refl₂ = refl

refl₃ : (A : Set) → (a : A) → a ≡ a
refl₃ A a = refl

refl₄ : (A : Set) (a : A) → a ≡ a
refl₄ A a = refl

refl₅ : ∀ {A} (a : A) → a ≡ a
refl₅ a = refl

refl₆ : ∀ A {a : A} → a ≡ a
refl₆ A = refl

refl₇ : ∀ A a → a ≡ a
refl₇ A a = refl {A = A} -- If we explicitly pass the argument A, Agda figures that `a : A`.



{-
Part 8: Decidable equality
=========================
-}
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

equalBool? : (x y : Bool) → Dec (x ≡ y)
equalBool? true true = yes refl
equalBool? true false = no (λ ())
equalBool? false true = no (λ ())
equalBool? false false = yes refl

-- Auxiliary function for an alternative solution to `equalNat?`
suc-injective : {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective {m} {.m} refl = refl

equalNat? : (m n : Nat) → Dec (m ≡ n)
equalNat? zero zero = yes refl
equalNat? zero (suc n) = no (λ ())
equalNat? (suc m) zero = no (λ ())
--
equalNat? (suc m) (suc n) with equalNat? m n
equalNat? (suc m) (suc n) | yes eq = yes (cong suc eq)
equalNat? (suc m) (suc n) | no neq = no (λ suc-m=suc-n → neq (cong (λ k → k - 1) suc-m=suc-n))
  -- this last clause can be done in several ways, here are two alternatives:
--equalNat? (suc m) (suc n) | no neq = no (λ{ refl → neq refl}) -- May not work in all versions of Agda.
--equalNat? (suc m) (suc n) | no neq = no (λ suc-m=suc-n → neq (suc-injective suc-m=suc-n))







-- Declaring precedence rules for operators (ignore this for now)
infixl  6 _∧_
infixl  5 _∨_
infix   4 if_then_else_
infixl 10 _+_
infixl 12 _*_
infix   2 _≡_
