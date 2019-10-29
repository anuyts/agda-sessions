
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
  e-If : {t1 t1' t2 t3 : Term} → t1 ↝ t1' → (tmIf t1 t2 t3 ↝ tmIf t1' t2 t3)
  e-Succ : {t1 t1' : Term} → t1 ↝ t1' → tmSucc t1 ↝ tmSucc t1'
  e-PredZero : tmPred tmZero ↝ tmZero
  e-PredSucc : {t : Term} → IsNumValue t → tmPred (tmSucc t) ↝ t
  e-Pred : {t t' : Term} → t ↝ t' → tmPred t ↝ tmPred t'
  e-IsZeroZero : tmIsZero tmZero ↝ tmTrue
  e-IsZeroSucc : {t : Term} → IsNumValue t → tmIsZero (tmSucc t) ↝ tmFalse
  e-IsZero : {t t' : Term} → t ↝ t' → tmIsZero t ↝ tmIsZero t'

IsNormal : Term → Set
IsNormal t = {t' : Term} → (t ↝ t') → ⊥

values-normal : {t : Term} → IsValue t → IsNormal t
values-normal {.tmTrue} valTrue {t'} ()
values-normal {.tmFalse} valFalse {t'} ()
values-normal {.tmZero} (valNum nvZero) {t'} ()
values-normal {.(tmSucc _)} (valNum (nvSucc x)) {.(tmSucc _)} (e-Succ et) = values-normal (valNum x) et

data _↝*_ : Term → Term → Set where
  done : {t : Term} → (t ↝* t)
  step_,_ : {t t' t'' : Term} → (t ↝ t') → (t' ↝* t'') → (t ↝* t'')
infixr 0 step_,_

s = tmIf tmTrue tmFalse tmFalse
t = tmIf s tmTrue tmTrue
test-eval1 : tmIf t tmFalse tmFalse ↝* tmFalse
test-eval1 = step e-If (e-If e-IfTrue) ,
             step e-If e-IfFalse ,
             step e-IfTrue ,
             done


-- Part 2: Untyped arithmetic terms
--=================================

-- Exercise: as a test, state and prove that
--   if false then 0 else (pred (suc (pred 0))) ↝* 0

test-eval2 : tmIf tmFalse tmZero (tmPred (tmSucc (tmPred tmZero))) ↝* tmZero
test-eval2 = step e-IfFalse ,
             step e-Pred (e-Succ e-PredZero) ,
             step e-PredSucc nvZero ,
             done



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
  d-If : {tyT : Type} → {t1 t2 t3 : Term} → (d1 : t1 ∈ tyBool) → (d2 : t2 ∈ tyT) → (d3 : t3 ∈ tyT)
    → tmIf t1 t2 t3 ∈ tyT
  d-Zero : tmZero ∈ tyNat
  d-Succ : {t : Term} → t ∈ tyNat → tmSucc t ∈ tyNat
  d-Pred : {t : Term} → t ∈ tyNat → tmPred t ∈ tyNat
  d-IsZero : {t : Term} → t ∈ tyNat → tmIsZero t ∈ tyBool

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
uniqueness-of-types {.tmTrue} {.tyBool} {.tyBool} d-True d-True = refl
uniqueness-of-types {.tmFalse} {.tyBool} {.tyBool} d-False d-False = refl
uniqueness-of-types {.(tmIf _ _ _)} {tyT1} {tyT2} (d-If d1 d3 d4) (d-If d2 d5 d6) = uniqueness-of-types d4 d6
uniqueness-of-types {.tmZero} {.tyNat} {.tyNat} d-Zero d-Zero = refl
uniqueness-of-types {.(tmSucc _)} {.tyNat} {.tyNat} (d-Succ d1) (d-Succ d2) = refl
uniqueness-of-types {.(tmPred _)} {.tyNat} {.tyNat} (d-Pred d1) (d-Pred d2) = refl
uniqueness-of-types {.(tmIsZero _)} {.tyBool} {.tyBool} (d-IsZero d1) (d-IsZero d2) = refl

-- Part 4: Safety = progress + preservation (see TAPL p. 96-97)
--=============================================================

-- First, prove the canonical forms lemma (lemma 8.3.1):
canonical-forms-bool : {t : Term} → (IsValue t) → (t ∈ tyBool) → (t ≡ tmTrue) ⊎ (t ≡ tmFalse)
canonical-forms-bool {.tmTrue} valTrue dt = left refl
canonical-forms-bool {.tmFalse} valFalse dt = right refl
canonical-forms-bool {.tmZero} (valNum nvZero) ()
canonical-forms-bool {.(tmSucc _)} (valNum (nvSucc x)) ()

canonical-forms-nat : {t : Term} → IsValue t → t ∈ tyNat → IsNumValue t
canonical-forms-nat {.tmTrue} valTrue ()
canonical-forms-nat {.tmFalse} valFalse ()
canonical-forms-nat {t} (valNum nvt) dt = nvt

preservation : {t                     t' : Term}    {tyT : Type} → (t ↝ t') → (t ∈ tyT)    → (t' ∈ tyT)
preservation {.tmTrue}               {t'}           {.tyBool} ()              d-True
preservation {.tmFalse}              {t'}           {.tyBool} ()              d-False
preservation {.(tmIf tmTrue _ _)}    {_}            {tyT}     e-IfTrue        (d-If d1 d2 d3) = d2
preservation {.(tmIf tmFalse _ _)}   {_}            {tyT}     e-IfFalse       (d-If d1 d2 d3) = d3
preservation {.(tmIf _ _ _)}         {.(tmIf _ _ _)}{tyT}     (e-If e1)       (d-If d1 d2 d3) =
     d-If (preservation e1 d1) d2 d3
preservation {.tmZero}               {t'}           {.tyNat}  ()              d-Zero
preservation {.(tmSucc _)}           {.(tmSucc _)}  {.tyNat}  (e-Succ e1)     (d-Succ d1)     = d-Succ (preservation e1 d1)
preservation {.(tmPred tmZero)}      {.tmZero}      {.tyNat}  e-PredZero      (d-Pred d1)     = d1
preservation {.(tmPred (tmSucc t'))} {t'}           {.tyNat}  (e-PredSucc x)  (d-Pred (d-Succ d1)) = d1
preservation {.(tmPred _)}           {.(tmPred _)}  {.tyNat}  (e-Pred e1)     (d-Pred d1)     = d-Pred (preservation e1 d1)
preservation {.(tmIsZero tmZero)}    {.tmTrue}      {.tyBool} e-IsZeroZero    (d-IsZero d1)   = d-True
preservation {.(tmIsZero (tmSucc _))}{.tmFalse}     {.tyBool} (e-IsZeroSucc x)(d-IsZero d1)   = d-False
preservation {.(tmIsZero _)}         {.(tmIsZero _)}{.tyBool} (e-IsZero e1)   (d-IsZero d1)   = d-IsZero (preservation e1 d1)

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
{-
-- With more implicit arguments:
progress {.tmTrue} {.tyBool} d-True = left valTrue
progress {.tmFalse} {.tyBool} d-False = left valFalse
progress {(tmIf t1 t2 t3)} {tyT} (d-If d1 d2 d3) with progress {t1} {tyBool} d1
progress {(tmIf t1 t2 t3)} {tyT} (d-If d1 d2 d3) | left v1 with canonical-forms-bool {t1} v1 d1
progress {tmIf .tmTrue t2 t3} {tyT} (d-If d1 d2 d3) | left v1 | left refl = right (t2 , e-IfTrue)
progress {tmIf .tmFalse t2 t3} {tyT} (d-If d1 d2 d3) | left v1 | right refl = right (t3 , e-IfFalse)
progress {(tmIf t1 t2 t3)} {tyT} (d-If d1 d2 d3) | right (t1' , e1) = right (tmIf t1' t2 t3 , e-If e1)
progress {.tmZero} {.tyNat} d-Zero = left (valNum nvZero)
progress {(tmSucc t1)} {.tyNat} (d-Succ d1) with progress {t1} {tyNat} d1
progress {tmSucc t1} {.tyNat} (d-Succ d1) | left (valNum nv1) = left (valNum (nvSucc nv1))
progress {tmSucc t1} {.tyNat} (d-Succ d1) | right (t1' , e1) = right (tmSucc t1' , e-Succ e1)
progress {(tmPred t1)} {.tyNat} (d-Pred d1) with progress {t1} {tyNat} d1
progress {tmPred .tmZero} {.tyNat} (d-Pred d1) | left (valNum nvZero) = right (tmZero , e-PredZero)
progress {tmPred (tmSucc t)} {.tyNat} (d-Pred d1) | left (valNum (nvSucc nvt)) = right (t , e-PredSucc nvt)
progress {tmPred t1} {.tyNat} (d-Pred d1) | right (t1' , e1) = right (tmPred t1' , e-Pred e1)
progress {(tmIsZero t1)} {.tyBool} (d-IsZero d1) with progress {t1} {tyNat} d1
progress {tmIsZero .tmZero} {.tyBool} (d-IsZero d1) | left (valNum nvZero) = right (tmTrue , e-IsZeroZero)
progress {tmIsZero (tmSucc t)} {.tyBool} (d-IsZero d1) | left (valNum (nvSucc nvt)) = right (tmFalse , e-IsZeroSucc nvt)
progress {tmIsZero t1} {.tyBool} (d-IsZero d1) | right (t1' , e1) = right (tmIsZero t1' , e-IsZero e1)
-}

-------------------------------------------------------
-- Challenge: Prove normalization of this calculus.

preservation* : {t t' : Term} {tyT : Type} → (t ↝* t') → (t ∈ tyT) → (t' ∈ tyT)
preservation* done dt = dt
preservation* (step et , et*) dt = preservation* et* (preservation et dt)

map* : {f : Term → Term}
  → (f↝ : {t t' : Term} → t ↝ t' → f t ↝ f t')
  → {t t' : Term} → t ↝* t' → f t ↝* f t'
map* f↝ done = done
map* f↝ (step et , et*) = step f↝ et , map* f↝ et*

step*_,_ : ∀ {t t' t''} → t ↝* t' → t' ↝* t'' → t ↝* t''
step* done , et* = et*
step* step et , et*' , et* = step et , step* et*' , et*
infixr 0 step*_,_

normalization : ∀ {t tyT} → t ∈ tyT → Σ[ t' ∈ Term ] ((t ↝* t') × IsValue t')
normalization d-True = tmTrue , done , valTrue
normalization d-False = tmFalse , done , valFalse
normalization (d-If dt1 dt2 dt3) with normalization dt1
normalization (d-If dt1 dt2 dt3) | t1' , e1* , v1' with canonical-forms-bool v1' (preservation* e1* dt1)
normalization (d-If dt1 dt2 dt3) | .tmTrue , e1* , v1' | left refl with normalization dt2
normalization (d-If dt1 dt2 dt3) | .tmTrue , e1* , v1' | left refl | t2' , e2* , v2' =
  t2' , (step* map* e-If e1* , step e-IfTrue , e2*) , v2'
normalization (d-If dt1 dt2 dt3) | .tmFalse , e1* , v1' | right refl with normalization dt3
normalization (d-If dt1 dt2 dt3) | .tmFalse , e1* , v1' | right refl | t3' , e3* , v3' =
  t3' , (step* map* e-If e1* , step e-IfFalse , e3*) , v3'
normalization d-Zero = tmZero , done , valNum nvZero
normalization (d-Succ dt) with normalization dt
normalization (d-Succ dt) | t' , e* , v' with canonical-forms-nat v' (preservation* e* dt)
normalization (d-Succ dt) | t' , e* , v' | nv' = tmSucc t' , map* e-Succ e* , valNum (nvSucc nv')
normalization (d-Pred dt) with normalization dt
normalization (d-Pred dt) | t' , e* , v' with canonical-forms-nat v' (preservation* e* dt)
normalization (d-Pred dt) | .tmZero , e* , v' | nvZero =
  tmZero , (step* map* e-Pred e* , step e-PredZero , done) , valNum (nvZero)
normalization (d-Pred dt) | (tmSucc t2) , e* , v' | nvSucc nv2 =
  t2 , (step* map* e-Pred e* , step e-PredSucc nv2 , done) , valNum nv2
normalization (d-IsZero dt) with normalization dt
normalization (d-IsZero dt) | t' , e* , v' with canonical-forms-nat v' (preservation* e* dt)
normalization (d-IsZero dt) | .tmZero , e* , v' | nvZero =
  tmTrue , (step* map* e-IsZero e* , step e-IsZeroZero , done) , valTrue
normalization (d-IsZero dt) | (tmSucc t2) , e* , v' | nvSucc nv2 =
  tmFalse , (step* map* e-IsZero e* , step e-IsZeroSucc nv2 , done) , valFalse
