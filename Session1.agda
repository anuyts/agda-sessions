{-

|--------------------------------------------------|
| Formal systems and their applications: exercises |
| Session 1: Agda basics                           |
|--------------------------------------------------|

Welcome to the exercise session on the Agda language! These exercise sessions are
meant to make you familiar with Agda and the agda-mode for emacs.

Agda is both a programming language and a proof assistant: you can use it to write
programs and then prove properties of these programs, and Agda will check these
proofs for you. Note that Agda is *not* an automatic prover, so you have to write
proofs yourself (though Agda can sometimes help you with that).

These exercises contain instructions and explanations that will help you to solve
them. These instructions are written in comments, either between {- -} or after -- 
and are ignored by Agda.

The full documentation of Agda can be found at agda.readthedocs.io


Part 1: Booleans and natural numbers
====================================

By default, Agda is a very barebones language with only one builtin type called Set,
so we have to define other types like numbers and booleans ourselves. Let's start by
defining the type of booleans. This is done by a 'data' declaration:
-}

data Bool : Set where
  true  : Bool
  false : Bool

{-
The first line of this definition declares a new type called Bool. The two subsequent
lines declare two terms of this type: true and false, both of type Bool. These are
called the constructors of the datatype. To check this definition, press C-c C-l in emacs.
(this means you have to press Ctrl+c followed by Ctrl+l). This 'loads' the file.
If everything goes right, the code will be colored and you get a list of unsolved goals
like "?0 : Bool". It's a good idea to (re)load the file often so you know everything is
still fine.

Next, let's define our first function: negation. Since Agda supports unicode syntax,
we can use the mathematical symbol '¬' for negation. In emacs, you can enter this
symbol by simply writing \lnot. Here are some other unicode symbols we will use:

   Type this...    to write this...
   \to             →
   \lnot           ¬
   \or or \vee     ∨
   \and or \wedge  ∧
   \_1, \_2, ...   ₁, ₂, ₃, ...
   \equiv or \==   ≡

The unicode input mode should be enabled by default in emacs, but you can enable 
or disable the unicode input mode by pressing Ctrl-\. 

Here is an incomplete definition of negation:
-}

¬ : Bool → Bool
¬ x = {!!}

{-
Take a look at the first line, this is the type declaration. It says
that ¬ is a function taking one argument of type Bool and returning a Bool.

The second line is the definition, but it is incomplete: it contains a hole.
Holes are parts of your Agda program that you haven't written yet. They are
useful because they allow you to typecheck some part of the program before
it's finished, and Agda can even give you the type of each hole. To add a hole
yourself, you can write ? or {!utter nonsense!} anywhere in your code and reload
the file with C-c C-l. The {!...!} approach is useful if you temporarily want to
replace some meaningful or erroneous code with a hole.

To complete the definition of ¬, place your cursor inside the hole and press
C-c C-c to perform a case split. Agda will ask you on which variable to do a
case split, type x and press enter. This will generate two cases: ¬ true = ?
and ¬ false = ?. To give the result in each of these cases, again place your
cursor inside the first hole, write the desired expression and press C-c C-space
to confirm.

Here is a list of some useful commands for interacting with Agda:

   C-c C-l         Load file
   C-c C-d         (after load) Deduce (infer) type of term
   C-c C-n         (after load) Normalize (evaluate) term
   C-c C-,         (inside hole) Information about hole
   C-c C-c         (inside hole) Case split
   C-c C-space     (inside hole) Give solution
   C-c C-r         (inside hole) Refine, using the goal's type and textual content
   C-u C-u <...>   Do <...> but produce normalized output

   C-g             Cancel whatever you're doing

More commands can be found in the Agda menu of Emacs, and even more online.

Now try to define 'and' and 'or' on booleans yourself by using case splitting.
These functions have type Bool → Bool → Bool. The arrow (→) is right associative,
so this should be read as Bool → (Bool → Bool), i.e. they are functions that take
one boolean and return another function that takes another boolean and returns a boolean.

The underscores in the names of a function mean that it uses mixfix syntax, 
the underscores are in the positions where the arguments should go.
-}

_∧_ : Bool → Bool → Bool
x ∧ y = {!!}

_∨_ : Bool → Bool → Bool
x ∨ y = {!!}

{-
Here is a polymorphic definition of the if-then-else function.
The accolad notation {A : Set} means that A is an implicit (i.e. hidden)
argument, so Agda tries to fill it in for you when you call the function.

(When you load your file and code gets highlighted yellow, this indicates
that Agda has failed to infer the value of an implicit argument.)
-}
if_then_else_ : {A : Set} → Bool → A → A → A
(if true  then x else y) = x
(if false then x else y) = y

{- We can give an alternative definition of negation in terms of if_then_else_: -}
¬-alt : Bool → Bool
¬-alt x = if x then false else true

{-
The type A can be any type, in particular also a function type
such as Bool → Bool → Bool. This is called a higher-order function because
it is a function that returns a function itself.
-}
weird : Bool → (Bool → Bool → Bool)
weird x = if x then _∧_ else _∨_

{-
To understand the definition of weird, you can ask Agda to evaluate
it for specific arguments. To do so, press C-c C-n, type in a term
(for example `weird false true false`) and press enter.

Next up, we will define (unary) natural numbers. A natural number is
either zero or the successor of another natural number:
-}
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{- 
This pragma allows you to write regular numbers 0,1,2,... instead of zero,
suc zero, suc (suc zero), ...:
-}
{-# BUILTIN NATURAL Nat #-}

{- Here is an example of a function on natural numbers: addition. -}
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

{- Now try to define the following functions yourself: -}
is-zero : Nat → Bool
is-zero n = {!!}

_-_ : Nat → Nat → Nat         -- Return zero instead of negative numbers
m - n = {!!}

minimum : Nat → Nat → Nat
minimum m n = {!!}

maximum : Nat → Nat → Nat
maximum m n = {!!}

_*_ : Nat → Nat → Nat
m * n = {!!}

{-
If Agda marks (part of) your definition in salmon-orange after you reload the file,
this means that Agda cannot see that your function is terminating. This is also the
case if you give an obviously non-terminating definition such as

f : Nat → Nat
f x = f x

Agda is a total language, so it will reject any not-obviously terminating function.
To make sure that Agda can see your function is terminating, write it in a way
that the arguments always become smaller in each recursive call.
-}

{-
Part 2: Proving basic properties
================================

Now as we said before, Agda is not just a programming language but also a proof
assistant. This means we can use Agda to formulate theorems and prove them,
and Agda will check that the proofs are correct.

Under the Curry-Howard correspondence, types correspond to propositions and
terms of a type correspond to a proof of the corresponding proposition. 
As an example, the type "A → B" in Agda corresponds to the proposition "A implies B".
Here are some other types corresponding to propositional logic.
-}

-- Trivial (top) type (unicode: \top). This corresponds to the proposition True.
data ⊤ : Set where
  tt : ⊤

-- Empty (bottom) type (unicode: \bot). This corresponds to the proposition False.
data ⊥ : Set where
  -- no constructors

-- Product type (unicode: \times or \x). This corresponds to the proposition "A and B".
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd p = {!!}

-- Sum type (unicode: \uplus). This corresponds to the proposition "A or B".
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

{- Prove the following propositions by giving a term of the given type: -}

-- "If A and B, then B and A"
-- hint: Agda is smart. After case 'splitting', try refining the goal using C-c C-r.
×-comm : {A B : Set} → A × B → B × A
×-comm p = {!!}

-- "If A and (B or C), then (A and B) or (A and C)"
-- Hint: use C-c C-, to see the type of variables in scope
distr : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
distr p = {!!}

-- Modus ponens: "If (A implies B) and A, then B"
app : {A B : Set} → (A → B) × A → B
app p = {!!}


{-
Part 3: Record types
====================
So far, we have defined types by giving their constructors, i.e. by specifying how we
can create elements of the type. We then used values of these types by case splitting
(pattern matching) over they were constructed.

We can also do the converse, and define a type by specifying how we can use its elements,
i.e. by specifying a list of fields that all elements must have. Then we can use values
of that type by using their fields, and we can create values by specifying the value of
each field. This provides an alternative way of defining the product type.

Types defined this way are called codata or record types. One way to create elements is
by using the constructor, whose arguments are simply the fields of the record. In this
sense, a record type can be regarded as an ordinary data type with exactly one constructor.

We can redefine the product type as a record type with two fields:
-}
record _×'_ (A B : Set) : Set where
  constructor _,'_
  field
    fst' : A
    snd' : B
{-
By default, we have to refer to the fields as _×'_.fst' and _×'_.snd'. By 'opening'
the module _×'_, we can simply write fst' and snd'
-}
open _×'_

{-
We can now create elements of the record type by co-pattern-matching, i.e. case splitting
over the field of the result that the function's caller will be interested in. Put the
cursor in the hole below, press C-c C-c and 'split on the result' by pressing enter
without providing a variable to pattern match over.
-}
×'-comm : {A B : Set} → A ×' B → B ×' A
×'-comm p = {!!}
{-
However, we can still treat _×'_ as a data type and prove commutativity of _×'_ in exactly
the same way we proved it for _×_, i.e. by pattern matching over p:
-}
×'-comm' : {A B : Set} → A ×' B → B ×' A
×'-comm' p = {!!}

{-
Part 4: The identity type
=========================

With only propositional logic, we won't be able to prove very interesting theorems.
This is where Agda's dependent types come in. They allow us to write any (functional)
property that we can think of as a type in Agda. In this exercise session, we give
only one example (albeit a very important one):

Something we often want to prove is that two things are equal, for example we want to
prove that ¬ (¬ true) is equal to true. For this purpose, we introduce the identity type
_≡_ (unicode input: \equiv or \==):
-}

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

{-
This is the first example we encounter of a dependent type: a type that depends
on values. In particular, we have the type 'x ≡ y' that depends on the values of
x and y. 

The terms of type 'x ≡ y' can be interpreted as proofs that x equals y.

The only constructor of this type is refl (short for reflexivity). Note that refl
only allows us to construct a term of type 'x ≡ x' for some x, so we can only
prove that a term is equal to itself. We will later see how we can derive the
other properties of equality (such as symmetry and transitivity).

One very useful application of the identity type is to write tests that are
automatically checked by Agda. For example, we can write a test that
¬ (¬ true) is equal to true:
-}

¬¬true : ¬ (¬ true) ≡ true
¬¬true = {!refl!}

{-
If you implemented the function ¬ correctly, you should be able to fill in
refl in the hole (using C-c C-space). To see what happens when you try to
prove a false statement, you can go back to the definition of ¬ and change
"¬ false = true" into "¬ false = false" and reload the file (using C-c C-l).

Note that identifiers in Agda can consist of almost any sequence of unicode 
characters. This also means that ¬¬true is not the same as ¬ (¬ true): the former is 
an identifier, while the latter is the double negation of true. So be sure to be 
liberal in your use of whitespace!

Hint: If you put the cursor in a hole and press C-u C-u C-c C-, then you get
normalized (C-u C-u <...>) information about the hole (C-c C-,), including
its normalized type. Above, this should be `true ≡ true`. Below, this
should be `3 ≡ 3`:
-}

3+5-5 : (3 + 5) - 5 ≡ 3
3+5-5 = {!!}

{-
If you want, you can try to come up with some additional tests about the functions
you defined earlier and implement them by using refl.
-}

-- Write more tests here

{-
You can also prove more general facts by adding arguments to a theorem, for example:
-}
¬¬-elim : (b : Bool) → ¬ (¬ b) ≡ b
{-
To prove this lemma, you cannot use refl straight away because Agda cannot see that
¬ (¬ b) is always equal to b from just the definition of ¬. Instead, you first have
to do a case split on b (using C-c C-c)
-}
¬¬-elim b = {!!}

{- Also try to prove the following lemmas: -}

∧-same : (b : Bool) → b ∧ b ≡ b
∧-same b = {!!}

if-same : {A : Set} → (b : Bool) (x : A) → (if b then x else x) ≡ x
if-same b x = {!!}


{-
Part 5: refl patterns and absurd patterns
=========================================

Here are some useful general properties of equality: symmetry, transitivity,
and congruence. To prove them, we have to match on a value of type x ≡ y, i.e.
a proof that x equals y. Since the only constructor of the identity type is
refl, there is always only one case. However, pattern matching on refl is not
useless: by pattern matching on a proof of x ≡ y, we learn something about
x and y, namely that they are the same.
In the definitions of `sym` and `trans` below, we make hidden arguments explicit.
Note that the third argument of sym is not {y}, but {.x}. The dot (.) here
indicates that the argument MUST be x for the pattern `refl` to make sense.
Agda fills out these dotted arguments automatically when you use C-c C-c.
-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym {A}{x}{.x} refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A}{x}{.x}{.x} refl refl = refl

{- Now try to prove congruence yourself: -}

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f {x}{y} p = {!!}

{-
If you have a proof of an absurd equality (for example true ≡ false),
you can write () in place to skip the proof. This is called an absurd pattern.
Agda allows you to skip this case because it is impossible to ever construct
a closed term of type 'true ≡ false' anyway.
-}
true-not-false : true ≡ false → ⊥
true-not-false ()

{-
Now use absurd patterns to prove that a natural number cannot be both zero and one.
You may have to do a non-absurd case split on one of the arguments first. Try three
different approaches:
-}
not-zero-and-one : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one n eq0 eq1 = {!!}

not-zero-and-one' : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one' n eq0 eq1 = {!!}

not-zero-and-one'' : (n : Nat) → n ≡ 0 → n ≡ 1 → ⊥
not-zero-and-one'' n eq0 eq1 = {!!}

{-
Here's another exercise: if 'b ∨ false' is equal to true, then b must be equal to true.
Hint: if you start by trying to pattern match on `eq`, you get a very interesting error
message.
-}
∨-first : (b : Bool) → b ∨ false ≡ true → b ≡ true
∨-first b eq = {!!}

{-
Finally, it is worth noting that equality proofs contain no information other than their
existence. Indeed, all proofs of the same equality are equal. This fact is called uniqueness
of identity proofs (UIP) and is by default provable in Agda:
-}
uip : {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
uip {A}{x}{y}{p}{q} = {!!}
{-
Homotopy Type Theory (HoTT), an active domain of research, investigates the virtues of
not having UIP and instead viewing equality proofs as data. This is beyond the scope
of the Formal Systems course.
The --without-K option in Agda disables the above proof of UIP. See the section titled
'Without K' in the Agda documentation for more information.
-}



{-
Part 6: More properties of natural numbers
==========================================

As people, we know that 0 + n = n = n + 0.
The first equality is easy to prove ...
-}
plus0-left : (n : Nat) → 0 + n ≡ n
plus0-left n = {!!}

{- ... but the second one is a bit harder. Can you guess why? -}
plus0-right : (n : Nat) → n + 0 ≡ n
plus0-right zero = {!!}
plus0-right (suc n) = {!!}
{-
hint 1: you can make a recursive call `plus0-right n` to get a proof of `n + 0 ≡ n`
        Under the Curry-Howard correspondence, a recursive function corresponds to
        a proof by induction.
hint 2: you may need to use the cong lemma from above to finish the proof.

Prove that addition on natural numbers is associative. Try to use as few cases
as possible. (It's possible to use only 2!)
-}
plus-assoc : (k l m : Nat) → k + (l + m) ≡ (k + l) + m
plus-assoc k l m = {!!}

{-
Now prove that addition is commutative. This proof is harder than the ones before,
so you may have to introduce a helper function to finish it.
-}
plus-comm : (m n : Nat) → m + n ≡ n + m
plus-comm m n = {!!}



{-
Part 7: Lambda-abstractions
===========================
So far, we have been defining named functions: each function is first declared
by giving its name and type, and then defined by giving one or more equations.
However, we can also define nameless functions inline. The syntax is

  λ args → body

You can input λ as \lambda or \Gl (Greek l). You can also use a backslash (\)
instead of λ, input \\ for that.

Prove the following lemma:
If (A or B) implies C, then A implies C and B implies C
-}
split-assumption : {A B C : Set} → (A ⊎ B → C) → (A → C) × (B → C)
split-assumption f = {!!}

--note that we do not need lambda-abstractions when we use _×'_:
split-assumption' : {A B C : Set} → (A ⊎ B → C) → (A → C) ×' (B → C)
fst' (split-assumption' f) a = {!!}
snd' (split-assumption' f) b = {!!}

{-
State and prove (using _×_):
If A implies (B and C), then A implies B and A implies C
-}



{-
We can also define inline pattern matching functions. The syntax is:

  λ { args-case1 → body-case1
    ; absurd-args-case2
    ; args-case3 → body-case3
    ...
    ; args-caseN → body-caseN
    }

Since the different arguments are separated just by spaces, a single argument
consisting of a pattern should be placed in parentheses, e.g. `(left x)`.

If the first argument's type is already empty, we can simply write `λ ()`.
-}
lemma : {A B : Set} → (A → B) → (A ⊎ ⊥ → B) × (⊥ → A)
lemma f = {!!}


{- 
Part 8: Decidable equality
=========================

A type is decidable if we can either give a concrete element of that type 
(`yes`) or prove that there is definitely no such element (`no`).
-}
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

{-
A decision procedure for a property P is a function that returns a decision
of `Dec (P x)` for every argument x. For example, we can decide whether two
booleans are equal:
-}
equalBool? : (x y : Bool) → Dec (x ≡ y)
equalBool? x y = {!!}

{-
Decidable equality for natural numbers is a little trickier because we need
a new piece of syntax called `with`. The `with` construct allows you to analyse
the value of a recursive call, which you need to complete the proof that equality
on natural numbers is decidable.
-}
equalNat? : (m n : Nat) → Dec (m ≡ n)
equalNat? zero zero = {!!}
equalNat? zero (suc n) = {!!}
equalNat? (suc m) zero = {!!}
-- 
equalNat? (suc m) (suc n) with equalNat? m n 
equalNat? (suc m) (suc n) | yes eq = {!!}
equalNat? (suc m) (suc n) | no neq = {!!}








-- Declaring precedence rules for operators (ignore this for now)
infixl  6 _∧_
infixl  5 _∨_
infix   4 if_then_else_
infixl 10 _+_
infixl 12 _*_
infix   2 _≡_
