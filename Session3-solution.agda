
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
  tmZero : Term
  tmSucc : Term → Term
  tmPred : Term → Term
  tmIsZero : Term → Term

size : Term → Nat
size tmTrue = 1
size tmFalse = 1
size (tmIf t t1 t2) = 1 + size t + size t1 + size t2
size tmZero = 1
size (tmSucc t) = suc (size t) 
size (tmPred t) = suc (size t)
size (tmIsZero t) = suc (size t)

data IsNumValue : Term → Set where
  nvZero : IsNumValue tmZero
  nvSucc : {t : Term} → IsNumValue t → IsNumValue (tmSucc t)

data IsValue : Term → Set where
  valTrue  : IsValue tmTrue
  valFalse : IsValue tmFalse
  valNum : {t : Term} → IsNumValue t → IsValue t

data _↝_ : Term → Term → Set where
  e-IfTrue : {t2 t3 : Term} → ((tmIf tmTrue t2 t3) ↝ t2)
  e-IfFalse : {t2 t3 : Term} → ((tmIf tmFalse t2 t3) ↝ t3)
  e-If : {t1 t1' t2 t3 : Term} → t1 ↝ t1' → tmIf t1 t2 t3 ↝ tmIf t1' t2 t3
  e-Succ : {t t' : Term} → t ↝ t' → tmSucc t ↝ tmSucc t'
  e-PredZero : tmPred tmZero ↝ tmZero
  e-PredSucc : ∀{t} → IsNumValue t → tmPred (tmSucc t) ↝ t
  e-Pred : ∀{t t'} → t ↝ t' → tmPred t ↝ tmPred t'
  e-IsZeroZero : tmIsZero tmZero ↝ tmTrue
  e-IsZeroSucc : ∀{t} → IsNumValue t → tmIsZero (tmSucc t) ↝ tmFalse
  e-IsZero : ∀{t t'} → t ↝ t' → tmIsZero t ↝ tmIsZero t'

IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥

values-normal : {t : Term} → IsValue t → IsNormal t
values-normal {.tmTrue} valTrue {t'} ()
values-normal {.tmFalse} valFalse {t'} ()
values-normal {.tmZero} (valNum nvZero) {t'} ()
values-normal {.(tmSucc _)} (valNum (nvSucc x)) {.(tmSucc _)} (e-Succ et) = values-normal (valNum x) et

data _↝*_ : Term → Term → Set where
  done : {x : Term} → (x ↝* x)
  step_,_ : {x x1 y : Term} → (x ↝ x1) → (x1 ↝* y) → (x ↝* y)
infixr 0 step_,_

s = tmIf tmTrue tmFalse tmFalse
t = tmIf s tmTrue tmTrue
test-eval1 : tmIf t tmFalse tmFalse ↝* tmFalse
test-eval1 = (
    step e-If (e-If e-IfTrue) ,
    step e-If e-IfFalse ,
    step e-IfTrue , done
  )


-- Part 2: Untyped arithmetic terms
--=================================

-- Exercise: as a test, state and prove that
--   if false then 0 else (pred (suc (pred 0))) ↝* 0

test-eval2 : tmIf tmFalse tmZero (tmPred (tmSucc (tmPred tmZero))) ↝* tmZero
test-eval2 = step e-IfFalse ,
               step e-Pred (e-Succ e-PredZero) , step e-PredSucc nvZero , done



-- Part 3: Typed arithmetic terms
--===============================
data Type : Set where
  tyBool : Type
  tyNat  : Type

-- As with the evaluation rules, we encode the typing rules as a data type
-- We use the unicode symbol ∈ (input ∈) instead of a colon because the colon
-- is already reserved by Agda.
data _∈_ : Term → Type → Set where
  d-True : tmTrue ∈ tyBool
  d-False : tmFalse ∈ tyBool
  d-If : ∀{tyT t1 t2 t3} → t1 ∈ tyBool → t2 ∈ tyT → t3 ∈ tyT → tmIf t1 t2 t3 ∈ tyT
  d-Zero : tmZero ∈ tyNat
  d-Succ : ∀{t} → t ∈ tyNat → tmSucc t ∈ tyNat
  d-Pred : ∀{t} → t ∈ tyNat → tmPred t ∈ tyNat
  d-IsZero : ∀{t} → t ∈ tyNat → tmIsZero t ∈ tyBool

test-typing : tmIf (tmIsZero tmZero) tmZero (tmPred tmZero) ∈ tyNat
test-typing = d-If (d-IsZero d-Zero) d-Zero (d-Pred d-Zero)

-- Inversion lemmas (see TAPL p. 94):
inversion-true : {tyR : Type} → tmTrue ∈ tyR → tyR ≡ tyBool
inversion-true {tyBool} d-True = refl

inversion-if : ∀ {tyR t1 t2 t3} → tmIf t1 t2 t3 ∈ tyR → (t1 ∈ tyBool) × ((t2 ∈ tyR) × (t3 ∈ tyR))
inversion-if (d-If d1 d2 d3) = d1 , (d2 , d3)

inversion-isZero : ∀ {tyR t} → tmIsZero t ∈ tyR → (tyR ≡ tyBool) × (t ∈ tyNat)
inversion-isZero (d-IsZero d) = refl , d


-- Uniqueness of types (see TAPL p. 94):
uniqueness-of-types : {t : Term} {tyT1 tyT2 : Type} → t ∈ tyT1 → t ∈ tyT2 → tyT1 ≡ tyT2
uniqueness-of-types d-True d-True = refl
uniqueness-of-types d-False d-False = refl
uniqueness-of-types (d-If d1 d2 d3) (d-If d4 d5 d6) =
  uniqueness-of-types d2 d5
uniqueness-of-types d-Zero d-Zero = refl
uniqueness-of-types (d-Succ d1) (d-Succ d2) = refl
uniqueness-of-types (d-Pred d1) (d-Pred d2) = refl
uniqueness-of-types (d-IsZero d1) (d-IsZero d2) = refl

-- Part 4: Safety = progress + preservation (see TAPL p. 96-97)
--=============================================================

-- First, prove the canonical forms lemma (lemma 8.3.1):
canonical-forms-bool : {t : Term} → (IsValue t) → (t ∈ tyBool) → (t ≡ tmTrue) ⊎ (t ≡ tmFalse)
canonical-forms-bool valTrue dt = left refl
canonical-forms-bool valFalse dt = right refl
canonical-forms-bool (valNum nvZero) ()
canonical-forms-bool (valNum (nvSucc x)) ()

canonical-forms-nat : {t : Term} → IsValue t → t ∈ tyNat → IsNumValue t
canonical-forms-nat valTrue ()
canonical-forms-nat valFalse ()
canonical-forms-nat (valNum x) dt = x

preservation : {t t' : Term} {T : Type} → (t ↝ t') → (t ∈ T) → (t' ∈ T)
preservation () d-True
preservation () d-False
preservation e-IfTrue (d-If d1 d2 d3) = d2
preservation e-IfFalse (d-If d1 d2 d3) = d3
preservation (e-If e1) (d-If d1 d2 d3) = d-If (preservation e1 d1) d2 d3
preservation () d-Zero
preservation (e-Succ e1) (d-Succ d1) = d-Succ (preservation e1 d1)
preservation e-PredZero (d-Pred d1) = d-Zero
preservation (e-PredSucc nv1) (d-Pred (d-Succ d1)) = d1
preservation (e-Pred e1) (d-Pred d1) = d-Pred (preservation e1 d1)
preservation e-IsZeroZero (d-IsZero d1) = d-True
preservation (e-IsZeroSucc nv1) (d-IsZero d1) = d-False
preservation (e-IsZero e1) (d-IsZero d1) = d-IsZero (preservation e1 d1)

progress : {t : Term} {tyT : Type} → t ∈ tyT → (IsValue t) ⊎ (Σ[ t' ∈ Term ] (t ↝ t'))
progress d-True = left valTrue
progress d-False = left valFalse
progress (d-If d1 d2 d3) with progress d1
progress (d-If d1 d2 d3) | left val1 with canonical-forms-bool val1 d1
progress (d-If d1 d2 d3) | left val1 | (left refl) = right (_ , e-IfTrue)
progress (d-If d1 d2 d3) | left val1 | (right refl) = right (_ , e-IfFalse)
progress (d-If d1 d2 d3) | right (t1' , e1) = right (tmIf t1' _ _ , e-If e1)
progress d-Zero = left (valNum nvZero)
progress (d-Succ d1) with progress d1
progress (d-Succ d1) | left val1 = left (valNum (nvSucc (canonical-forms-nat val1 d1)))
progress (d-Succ d1) | right (t1' , e1) = right (tmSucc t1' , e-Succ e1)
progress (d-Pred d1) with progress d1
progress (d-Pred d1) | left val1 with canonical-forms-nat val1 d1
progress (d-Pred d1) | left val1 | nvZero = right (tmZero , e-PredZero)
progress (d-Pred d1) | left val1 | (nvSucc u) = right (_ , e-PredSucc u)
progress (d-Pred d1) | right (t1' , e1) = right (tmPred t1' , e-Pred e1)
progress (d-IsZero d1) with progress d1
progress (d-IsZero d1) | left val1 with canonical-forms-nat val1 d1
progress (d-IsZero d1) | left val1 | nvZero = right (tmTrue , e-IsZeroZero)
progress (d-IsZero d1) | left val1 | (nvSucc u) = right (tmFalse , e-IsZeroSucc u)
progress (d-IsZero d1) | right (t1' , e1) = right (tmIsZero t1' , e-IsZero e1)

-------------------------------------------------------
-- Challenge: Prove normalization of this calculus.

preservation* : {t t' : Term} {tyT : Type} → (t ↝* t') → (t ∈ tyT) → (t' ∈ tyT)
preservation* done dt = dt
preservation* (step et , et*) dt = preservation* et* (preservation et dt)

map* : {f : Term → Term}
  → (f↝ : {t t' : Term} → t ↝ t' → f t ↝ f t')
  → {t t' : Term} → t ↝* t' → f t ↝* f t'
map* f↝ done = done
map* f↝ (step t↝t'' , t''↝*t') = step f↝ t↝t'' , map* f↝ t''↝*t'

step*_,_ : ∀ {t t' t''} → t ↝* t' → t' ↝* t'' → t ↝* t''
step* done , et* = et*
step* step et , et*' , et* = step et , step* et*' , et*
infixr 0 step*_,_

normalization : ∀ {t tyT} → t ∈ tyT → Σ[ t' ∈ Term ] ((t ↝* t') × IsValue t')
normalization d-True = tmTrue , (done , valTrue)
normalization d-False = tmFalse , (done , valFalse)
normalization (d-If d1 d2 d3) with normalization d1
normalization (d-If d1 d2 d3) | t1' , (e*1 , val1') with canonical-forms-bool val1' (preservation* e*1 d1)
normalization (d-If d1 d2 d3) | .tmTrue , (e*1 , val-true) | (left refl) with normalization d2
normalization (d-If d1 d2 d3) | .tmTrue , (e*1 , val-true) | (left refl) | (t2' , (e*2 , val2')) =
  t2' , ((step* map* e-If e*1 , step e-IfTrue , e*2) , val2')
normalization (d-If d1 d2 d3) | .tmFalse , (e*1 , val-false) | (right refl) with normalization d3
normalization (d-If d1 d2 d3) | .tmFalse , (e*1 , val-false) | (right refl) | (t3' , (e*3 , val3')) =
  t3' , ((step* map* e-If e*1 , step e-IfFalse , e*3) , val3')
normalization d-Zero = tmZero , (done , valNum nvZero)
normalization (d-Succ d1) with normalization d1
normalization (d-Succ d1) | t1' , (e*1 , val1') =
  (tmSucc t1') , ((map* e-Succ e*1) , valNum (nvSucc (canonical-forms-nat val1' (preservation* e*1 d1))))
normalization (d-Pred d1) with normalization d1
normalization (d-Pred d1) | t1' , (e*1 , val1') with canonical-forms-nat val1' (preservation* e*1 d1)
normalization (d-Pred d1) | .tmZero , (e*1 , val-zero) | nvZero =
  tmZero , ((step* map* e-Pred e*1 , step e-PredZero , done) , valNum nvZero)
normalization (d-Pred d1) | .(tmSucc _) , (e*1 , val-succ-t2) | (nvSucc nv-t) =
  _ , ((step* map* e-Pred e*1 , step e-PredSucc nv-t , done) , (valNum nv-t))
normalization (d-IsZero d1) with normalization d1
normalization (d-IsZero d1) | t1' , (e*1 , val1') with canonical-forms-nat val1' (preservation* e*1 d1)
normalization (d-IsZero d1) | .tmZero , (e*1 , val-zero) | nvZero =
  tmTrue , ((step* map* e-IsZero e*1 , step e-IsZeroZero , done) , valTrue)
normalization (d-IsZero d1) | .(tmSucc _) , (e*1 , val-succ-t2) | (nvSucc nv-t) =
  tmFalse , ((step* map* e-IsZero e*1 , step e-IsZeroSucc nv-t , done) , valFalse)
