
{-

|---------------------------------------------------|
| Formal systems and their applications: exercises  |
| Session 3: Formalization of programming languages |
|---------------------------------------------------|

-}

open import Data.Nat renaming (ℕ to Nat ; _≟_ to equalNat?) hiding (pred ; _≤_ ; compare)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum hiding (map) renaming (inj₁ to left ; inj₂ to right)


-- Part 1: Untyped boolean terms
--==============================
data Term : Set where
  tmTrue   : Term
  tmFalse  : Term
  tmIf     : (t1 t2 t3 : Term) → Term

size : Term → Nat
size tmTrue = 1
size tmFalse = 1
size (tmIf t t1 t2) = 1 + size t + size t1 + size t2

data IsValue : Term → Set where
  valTrue  : IsValue tmTrue
  valFalse : IsValue tmFalse

data _↝_ : Term → Term → Set where
  e-IfTrue : {t2 t3 : Term} → (tmIf tmTrue t2 t3 ↝ t2)
  e-IfFalse : {t2 t3 : Term} → (tmIf tmFalse t2 t3 ↝ t3)
  e-If : {t1 t1' t2 t3 : Term} → t1 ↝ t1' → tmIf t1 t2 t3 ↝ tmIf t1' t2 t3

IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥
values-normal : {t : Term} → IsValue t → IsNormal t
values-normal {.tmTrue} valTrue ()
values-normal {.tmFalse} valFalse ()

data _↝*_ : Term → Term → Set where
  done : {x : Term} → (x ↝* x)
  step_,_ : {x x1 y : Term} → (x ↝ x1) → (x1 ↝* y) → (x ↝* y)
infixr 0 step_,_

s = tmIf tmTrue tmFalse tmFalse
t = tmIf s tmTrue tmTrue
test-eval1 : tmIf t tmFalse tmFalse ↝* tmFalse
test-eval1 = step e-If (e-If e-IfTrue) ,
             step e-If e-IfFalse ,
             step e-IfTrue ,
             done
